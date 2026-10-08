(defpackage #:snowgrave.method-call-bindings.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass #:defgeneric #:defmethod))
(in-package #:snowgrave.tests)

(defun method-source-context-tests ()
  (let* ((package (or (find-package "SNOWGRAVE.METHOD-SOURCE.CONTROL")
                      (make-package "SNOWGRAVE.METHOD-SOURCE.CONTROL" :use '("COMMON-LISP"))))
         (*package* package)
         (forms (read-from-string
           "((defclass holder () ((callback :initarg :callback)))
             (defgeneric invoke-owner (owner))
             (defmethod invoke-owner ((owner holder)) (funcall (slot-value owner 'callback)))
             (defun run-owner (owner) (invoke-owner owner)))"))
         (identity '(:method-source-context))
         (condition (handler-case
                        (snowgrave:close-source-unit (list :forms forms) :unit-name identity
                          :closed-classes (list (intern "HOLDER")) :universe (list (intern "HOLDER"))
                          :closed-generics (list (intern "INVOKE-OWNER")) :entries (list (intern "RUN-OWNER"))
                          :external-domains (list (list (intern "RUN-OWNER") (list (intern "HOLDER")))))
                      (snowgrave:unclosed-call (condition) condition))))
    (check (typep condition 'snowgrave:unclosed-call))
    (check (eq (snowgrave:error-feature condition) :computed-function))
    (check (equal (snowgrave:error-source-key condition) (list identity 3)))))

(defun method-call-binding-tests ()
  (let* ((*package* (find-package :snowgrave.method-call-bindings.fixture))
         (base (intern "BASE")) (leaf (intern "LEAF")) (trace (intern "*TRACE*"))
         (prefix (read-from-string
          "((defclass base () ((payload :initarg :payload))) (defclass leaf (base) ())
            (defparameter *trace* nil)
            (defgeneric amount (r))
            (defmethod amount ((r base)) (values (slot-value r 'payload) :amount))
            (defgeneric twice (r))
            (defmethod twice ((r base)) (values (* 2 (slot-value r 'payload)) :twice))
            (defgeneric optional (r &optional callback))
            (defmethod optional :around ((r leaf) &optional
                  (callback (progn (push :around-default *trace*) #'twice) suppliedp))
              (declare (ignore callback))
              (push (if suppliedp :around-provided :around-omitted) *trace*)
              (unwind-protect (call-next-method) (push :around-cleanup *trace*)))
            (defmethod optional :before ((r base) &optional
                  (callback (progn (push :before-default *trace*) #'amount) suppliedp))
              (declare (ignore callback)) (push (if suppliedp :before-provided :before-omitted) *trace*))
            (defmethod optional :after ((r base) &optional
                  (callback (progn (push :after-default *trace*) #'amount) suppliedp))
              (declare (ignore callback)) (push (if suppliedp :after-provided :after-omitted) *trace*))
            (defmethod optional ((r base) &optional
                  (callback (progn (push :primary-default *trace*) #'amount) suppliedp))
              (multiple-value-bind (value tag) (funcall callback r) (values value tag suppliedp)))
            (defgeneric keyed (r &key callback))
            (defmethod keyed :before ((r base) &key callback extra)
              (declare (ignore callback))
              (push (if extra :extra :no-extra) *trace*))
            (defmethod keyed ((r base) &key
                  ((:callback callback) (progn (push :key-default *trace*) #'amount) suppliedp))
              (multiple-value-bind (value tag) (funcall callback r) (values value tag suppliedp)))
            (defgeneric presence (r &optional value))
            (defmethod presence ((r base) &optional (value (progn (push :presence-default *trace*) 17) suppliedp))
              (values value suppliedp))
            (defgeneric pack (r &optional callback))
            (defmethod pack ((r base) &optional (callback #'amount)) (values :tag r callback))
            (defgeneric (setf receipt) (value r &optional callback))
            (defmethod (setf receipt) ((value number) (r base) &optional (callback #'amount))
              (values (funcall callback r) value))
            (defun method-relay (r) (optional r))
            (defun key-name () :callback)
            (defgeneric caller (r)) (defmethod caller ((r base)) (method-relay r))
            (defun boot-base (n) (make-instance 'base :payload n))
            (defun boot (n) (make-instance 'leaf :payload n)))"))
         (bodies '("(optional r)" "(optional r #'twice)" "(funcall #'optional r)"
                   "(apply #'optional (list r))" "(apply #'optional r (list #'twice))"
                   "(multiple-value-call #'optional (values r) (values #'twice))"
                   "(keyed r)" "(keyed r :callback #'twice)"
                   "(keyed r :callback #'amount :callback #'twice)"
                   "(keyed r :extra t)" "(keyed r :extra nil)"
                   "(keyed r (key-name) #'twice)"
                   "(apply #'keyed r (list :callback #'twice))"
                   "(presence r)" "(presence r nil)"
                   "(multiple-value-bind (tag object callback) (pack r)
                       (values (slot-value object 'payload) (funcall callback object) tag))"
                   "(multiple-value-bind (tag object callback) (pack r #'twice)
                       (values (slot-value object 'payload) (funcall callback object) tag))"
                   "(funcall #'(setf receipt) 19 r)" "(funcall #'(setf receipt) 19 r #'twice)"
                   "(caller r)"))
         (entries (loop for i below (length bodies) collect (intern (format nil "ENTRY-~D" i))))
         (forms (append prefix (loop for entry in entries for body in bodies
                                    collect `(defun ,entry (,(intern "R")) ,(read-from-string body)))))
         (generics (read-from-string "(amount twice optional keyed presence pack (setf receipt) caller)"))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(method-call-bindings)
                :closed-classes (list base leaf) :closed-generics generics :universe (list base leaf 'number)
                :entries (append (read-from-string "(boot boot-base)") entries)
                :external-domains (append (read-from-string "((boot (number)) (boot-base (number)))")
                                          (mapcar (lambda (entry) (list entry (list base))) entries))))
         (expected nil))
    (dolist (form forms) (eval form))
    (dolist (class (list base leaf))
      (dolist (n '(17 -3))
        (let ((native (make-instance class :payload n))
              (record (funcall (test-unit-function unit (if (eq class base) "BOOT-BASE" "BOOT")) n)))
          (dolist (entry entries)
            (setf (symbol-value trace) nil)
            (let ((values (multiple-value-list (funcall entry native)))
                  (effects (reverse (symbol-value trace))))
              (setf (symbol-value trace) nil)
              (check (equal values (multiple-value-list (funcall (snowgrave:unit-function unit entry) record))))
              (check (equal effects (reverse (symbol-value trace))))
              (push (list (symbol-name entry) (symbol-name class) n values effects) expected))))))
    (check (eq (getf (getf (snowgrave:unit-report unit) :ordinary-function-flow) :generic-binding-method)
               :raw-call-shapes-through-shared-lambda-owner))
    ;; A finite set of observed direct callers is never an arbitrary-callers
    ;; proof. Escape and variable APPLY must poison nonrequired binding facts.
    (labels ((refused (body domains)
               (let* ((bad (intern "BAD")) (good (intern "GOOD")) (r (intern "R")) (x (intern "X")))
                 (check (handler-case
                   (snowgrave:close-source-unit
                    (list :forms (append prefix (list `(defun ,bad (,r ,x) ,(read-from-string body))
                                                      `(defun ,good (,r)
                                                         ,(read-from-string "(progn (optional r) (keyed r) (presence r) (pack r)
                                                                                    (funcall #'(setf receipt) 0 r) (caller r))")))))
                    :unit-name (list :unproved-method-calls body)
                    :closed-classes (list base leaf) :closed-generics generics :universe (list base leaf 'number 'function)
                    :entries (list good bad) :external-domains (list (list good (list base)) (list bad domains)))
                   (snowgrave:unclosed-call (condition) (eq (snowgrave:error-feature condition) :computed-function)))))))
      (refused "(optional r x)" (list base 'function))
      (refused "(apply #'optional r x)" (list base t))
      (refused "(progn (optional r) #'optional)" (list base t))
      (refused "(keyed r :callback x)" (list base 'function)))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-method-call-bindings.lisp" root))
           (metadata (merge-pathnames ".build/fresh-method-call-bindings.metadata" root))
           (observations (merge-pathnames ".build/fresh-method-call-bindings.expected" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (with-open-file (stream observations :direction :output :if-exists :supersede) (write (nreverse expected) :stream stream :readably t))
      (check (search "Fresh method call bindings executed."
                     (uiop:run-program
                      (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                            (namestring (merge-pathnames "scripts/fresh-method-call-bindings.lisp" root))
                            (namestring source) (namestring metadata) (namestring observations)) :output :string))))))
