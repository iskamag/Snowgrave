(in-package #:snowgrave.tests)

(defun partition-factorization-tests ()
  (let* ((*package* (or (find-package "SNOWGRAVE.PARTITION.FIXTURE")
                       (make-package "SNOWGRAVE.PARTITION.FIXTURE" :use '("COMMON-LISP"))))
         (forms (read-from-string
          "((defclass visitor () ((id :initarg :id))) (defclass fast (visitor) ())
            (defclass foreign () ()) (defparameter *log* nil)
            (defgeneric visit (v a b c d e f g))
            (defmethod visit :around ((v visitor) a b c d e f g)
              (declare (ignore a b c d e f g)) (push :around *log*)
              (unwind-protect (call-next-method) (push :cleanup *log*)))
            (defmethod visit :before ((v visitor) a b c d e f g)
              (declare (ignore a b c d e f g)) (push :before *log*))
            (defmethod visit :after ((v visitor) a b c d e f g)
              (declare (ignore a b c d e f g)) (push :after *log*))
            (defmethod visit ((v visitor) a b c d e f g)
              (push :base *log*)
              (values (if (typep a 'visitor) (slot-value a 'id) 0) a b c d e f g))
            (defmethod visit ((v fast) a b c d e f g)
              (declare (ignore a b c d e f g)) (push :fast *log*) (call-next-method))
            (defun boot (id) (make-instance 'visitor :id id))
            (defun boot-fast (id) (make-instance 'fast :id id))
            (defun run (v a b c d e f g) (visit v a b c d e f g)))"))
         (classes (mapcar #'intern '("VISITOR" "FAST" "FOREIGN")))
         (generic (intern "VISIT")) (boot (intern "BOOT")) (fast (intern "BOOT-FAST"))
         (run (intern "RUN")) (log (intern "*LOG*"))
         (unit (snowgrave:close-source-unit (list :forms forms) :unit-name '(factored-eight-axis-visitor)
                 :closed-classes classes :universe (append classes '(number t))
                 :closed-generics (list generic) :entries (list boot fast run)
                 :external-domains (list (list boot '(number)) (list fast '(number))
                                         (list run (cons (first classes) (make-list 7 :initial-element t))))))
         (dispatch (first (getf (snowgrave:unit-metadata unit) :dispatch)))
         (axes (getf dispatch :axis-uniformity)))
    (check (equal (mapcar (lambda (axis) (getf axis :position)) axes) '(1 2 3 4 5 6 7)))
    (check (= 17 (length (getf dispatch :cells))))
    (check (= (* 3 7 17) (getf dispatch :uniformity-replays)))
    (check (every (lambda (axis) (eq :standard-universal-specializer (getf axis :proof))) axes))
    (check (every (lambda (axis) (= 17 (length (getf axis :classes)))) axes))
    ;; Used T-specialized parameters retain their arbitrary values. Nothing
    ;; lets a method body treat A as the first concrete class representative.
    (dolist (form forms) (eval form))
    (loop for native in (list (funcall boot 17) (funcall fast 29))
          for record in (list (funcall (snowgrave:unit-function unit boot) 17)
                             (funcall (snowgrave:unit-function unit fast) 29))
          for expected-log in '((:around :before :base :after :cleanup)
                                (:around :before :fast :base :after :cleanup)) do
      (loop for native-value in (list nil 17 :tag #\x "native" (vector :native) native)
            for value in (list nil 17 :tag #\x "native" (vector :native) record) do
        (let* ((native-arguments (list native-value :b 3 #\c "text" nil native-value))
               (arguments (list value :b 3 #\c "text" nil value))
               (ordinary
                 (progv (list log) (list nil)
                   (prog1 (multiple-value-list (apply run native native-arguments))
                     (check (equal (reverse (symbol-value log)) expected-log)))))
               (closed
                 (progv (list log) (list nil)
                   (prog1 (multiple-value-list (apply (snowgrave:unit-function unit run) record arguments))
                     (check (equal (reverse (symbol-value log)) expected-log))))))
          (check (= (length ordinary) (length closed) 8))
          (check (eql (first ordinary) (first closed)))
          (check (every #'eq (cdr closed) arguments))
          (check (every #'eq (cdr ordinary) native-arguments)))))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-partition.lisp" root))
           (metadata (merge-pathnames ".build/fresh-partition.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh eight-axis visitor executed."
                     (uiop:run-program
                       (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                             (namestring (merge-pathnames "scripts/fresh-partition.lisp" root))
                             (namestring source) (namestring metadata)) :output :string))))
    ;; The stock-normalization certificate is not a whitelist for arbitrary
    ;; MOP overrides. A real delegating customization keeps the old full cells.
    (let ((method nil))
      (unwind-protect
           (sb-ext:without-package-locks
             (setf method
               (eval '(cl:defmethod sb-mop:compute-applicable-methods-using-classes :around
                        ((generic standard-generic-function) classes)
                        (declare (ignore classes)) (call-next-method))))
             (let* ((fallback (intern "FALLBACK")) (entry (intern "FALLBACK-RUN"))
                    (control (snowgrave:close-source-unit
                               (list :forms (append (subseq forms 0 3)
                                                   (list `(defgeneric ,fallback (v a))
                                                         `(defmethod ,fallback ((v ,(first classes)) a)
                                                            (declare (ignore v a)) :ok)
                                                         `(defun ,entry (v a) (,fallback v a)))))
                               :unit-name '(custom-mop-concrete-partition)
                               :closed-classes classes :universe (append classes '(number t))
                               :closed-generics (list fallback) :entries (list entry)
                               :external-domains (list (list entry (list (first classes) t)))))
                    (description (first (getf (snowgrave:unit-metadata control) :dispatch))))
               (check (null (getf description :axis-uniformity)))
               (check (zerop (getf description :uniformity-replays)))
               (check (= (* 17 17) (length (getf description :cells))))
               (let ((visitor (funcall (snowgrave:unit-function unit boot) 17)))
                 ;; Independent units have independent layout identities.
                 (signals snowgrave:domain-violation
                   (funcall (snowgrave:unit-function control entry) visitor :anything)))))
        (when method (remove-method #'sb-mop:compute-applicable-methods-using-classes method))))))
