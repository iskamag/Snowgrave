;;;; Target-only cold bridge from a frozen ordinary MOP snapshot to real native
;;;; structures. CEM bodies are supplied by the source adapter, never rebuilt.
(in-package #:snowgrave.mezzano-materializer)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *native-unit-layouts* (make-hash-table :test #'equal))

  (defun literal-value (form)
    (unless (and (consp form) (eq (car form) 'quote) (null (cddr form)))
      (error "Native record ABI needs an exact compiler-owned literal: ~S" form))
    (second form))

  (defun admitted-logical-layout (arguments layouts)
    "Resolve a complete cold logical row before emitting its native header test."
    (let* ((identity (literal-value (first arguments)))
           (class (literal-value (second arguments)))
           (layout (find class layouts :key (lambda (row) (getf row :class))))
           (keys (nthcdr 4 arguments)))
      (unless (and layout (equal identity (getf layout :identity))
                   (equal (literal-value (third arguments)) (getf layout :ancestors))
                   (equal (literal-value (fourth arguments)) (getf layout :slots))
                   (equal (literal-value (getf keys :slot-types)) (getf layout :slot-types))
                   (equal (literal-value (getf keys :error-mapping)) (getf layout :error-mapping))
                   (evenp (length keys))
                   (loop for (key value) on keys by #'cddr
                         always (and (member key '(:slot-types :error-mapping :reference-domain))
                                     ;; Native class-reference families need
                                     ;; their own physical field/type mapping.
                                     (or (not (eq key :reference-domain)) (null value)))))
        (error "Changed or unmapped logical record descriptor in native source."))
      layout))

  (defun native-slot-domain (type)
    (multiple-value-bind (domain validp) (snowgrave.mezzano-access::record-slot-domain type)
      (when validp (return-from native-slot-domain domain)))
    (labels ((array-domain-p (x)
               (and (consp x) (eq (car x) 'simple-array) (= (length x) 3)
                    (equal (third x) '(*))
                    (member (second x) '((unsigned-byte 8) (unsigned-byte 16) (unsigned-byte 32))
                            :test #'equal))))
      (cond ((array-domain-p type) type)
            ((and (consp type) (eq (car type) 'or) (eq (second type) 'null)
                  (cddr type) (every #'array-domain-p (cddr type))) type)
            (t (error "No allocation-free native field domain for ~S" type)))))

  (defun domain-test (value type)
    (cond ((and (consp type) (eq (car type) 'simple-array))
           (let ((tag (ecase (second (second type))
                        (8 mezzano.internals::+object-tag-array-unsigned-byte-8+)
                        (16 mezzano.internals::+object-tag-array-unsigned-byte-16+)
                        (32 mezzano.internals::+object-tag-array-unsigned-byte-32+))))
             (snowgrave.mezzano-access::array-tag-test value tag)))
          ((and (consp type) (eq (car type) 'or))
           `(or (null ,value) ,@(mapcar (lambda (x) (domain-test value x)) (cddr type))))
          (t (snowgrave.mezzano-access::record-domain-test value type))))

  (defun header-test (record layout)
    `(and (mezzano.internals::%value-has-tag-p ,record mezzano.internals::+tag-object+)
          (mezzano.internals::%fast-instance-layout-eq-p ,record ',(getf layout :header))))

  (defun slot-access (record slot)
    `(,(getf slot :primitive) ,record ,(getf slot :index)))

  (defun bound-access (record slot)
    `(mezzano.internals::%%object-ref-unsigned-byte-32-unscaled ,record ,(getf slot :bound-offset)))

  (defun bound-test (record slot)
    `(not (eql (mezzano.runtime::%fixnum-logand ,(bound-access record slot) ,(getf slot :mask)) 0)))

  (defun type-failure (value type)
    `(error 'type-error :datum ,value :expected-type ',type))

  (defun field-operation (operation record value slot)
    (let* ((type (getf slot :type)) (domain (getf slot :domain))
           (access (slot-access record slot)) (bound (bound-access record slot))
           (mask (getf slot :mask)) (name (getf slot :name)))
      (ecase operation
        (:boundp (bound-test record slot))
        (:unbind `(progn
                    (setf ,bound (mezzano.runtime::%fixnum-logand ,bound ,(lognot mask)))
                    (setf ,access ,(if (getf slot :numeric) 0 nil)) nil))
        (:write `(if ,(domain-test value domain)
                     (progn (setf ,access ,value)
                            (setf ,bound (mezzano.runtime::%fixnum-logior ,bound ,mask)) ,value)
                     ,(type-failure value type)))
        (:read (let ((actual (gensym "SLOT")))
                 `(if ,(bound-test record slot)
                      (let ((,actual ,access))
                        (if ,(domain-test actual domain) ,actual ,(type-failure actual type)))
                      (,(getf slot :unbound-helper) ,record)))))))


  (defun expand-record-operation (operation arguments layouts)
    (let ((record (gensym "RECORD")) (value (gensym "VALUE")))
      (case operation
        ((:read :write :boundp :unbind)
         (let* ((writerp (eq operation :write))
                (slot (literal-value (second arguments)))
                (classes (literal-value (nth (if writerp 3 2) arguments)))
                (selected (mapcar (lambda (class)
                                   (or (find class layouts :key (lambda (x) (getf x :class)))
                                       (error "Foreign logical layout annotation ~S" class))) classes)))
           (unless selected (error "Empty native record receiver proof."))
           `(let ((,record ,(first arguments)) ,@(when writerp `((,value ,(third arguments)))))
              (cond ,@(mapcar
                       (lambda (layout)
                         (let ((field (find slot (getf layout :fields) :key (lambda (x) (getf x :name)))))
                           (unless field
                             (error "Missing-slot ABI for ~S.~S is not admitted on Mezzano."
                                    (getf layout :class) slot))
                           `(,(header-test record layout) ,(field-operation operation record value field)))) selected)
                    (t ,(type-failure record (cons 'or (mapcar (lambda (x) (getf x :native-class)) selected))))))))
        (:class `(let ((,record ,(first arguments)))
                   (cond ,@(mapcar (lambda (layout) `(,(header-test record layout) ',(getf layout :class-token))) layouts)
                         (t ,(type-failure record (cons 'or (mapcar (lambda (x) (getf x :native-class)) layouts)))))))
        ((:p :typep :unitp :layoutp)
         (let* ((selected
                  (case operation
                    (:p layouts)
                    (:typep (let ((class (literal-value (second arguments))))
                              (remove-if-not (lambda (x) (member class (getf x :ancestors))) layouts)))
                    (:unitp (let ((identity (literal-value (second arguments))))
                              (remove-if-not (lambda (x) (equal identity (first (getf x :identity)))) layouts)))
                    (:layoutp
                     (list (admitted-logical-layout (rest arguments) layouts))))))
           `(let ((,record ,(first arguments))) (or ,@(mapcar (lambda (x) (header-test record x)) selected)))))
        (otherwise (error "Unsupported native record operation ~S" operation)))))

  (defun finalize-native-layouts (descriptions)
    ;; Validate the entire actual native family before installing compiler
    ;; macros. No proposed byte offset or hand-written packing algorithm.
    (mapcar
     (lambda (description)
       (let* ((class (mezzano.internals::get-structure-type (getf description :native-class)))
              (layout (mezzano.clos:class-layout class))
              (slots (mezzano.clos:class-slots class))
              (fields nil))
         (unless (and layout (mezzano.clos:class-sealed class)) (error "Unsealed materialized class."))
         (loop for name in (getf description :slots) for type in (getf description :slot-types)
               for position from 0
               for domain = (native-slot-domain type)
               for slot = (find name slots :key #'mezzano.clos:slot-definition-name)
               for bound-name = (nth (floor position 32) (getf description :bound-names))
               for bound-slot = (find bound-name slots :key #'mezzano.clos:slot-definition-name)
               do (unless (and slot bound-slot) (error "Native slot family is incomplete."))
               collect
               (let* ((location (mezzano.clos:slot-definition-location slot))
                      (numeric (and (consp domain) (member (car domain) '(signed-byte unsigned-byte))))
                      (offset (mezzano.runtime::location-offset location))
                      (accessor (mezzano.runtime::location-type-accessor (mezzano.runtime::location-type location)))
                      (primitive (if numeric (intern (concatenate 'string "%" (symbol-name accessor))
                                                     (symbol-package accessor)) accessor)))
                 (multiple-value-bind (expected size)
                     (mezzano.internals::compute-struct-slot-accessor-and-size (if numeric domain t))
                   (unless (and (eql expected (mezzano.runtime::location-type location))
                                (zerop (mod offset size))
                                (<= (+ offset size) (* 8 (mezzano.internals::layout-heap-size layout))))
                     (error "Actual native field differs from logical domain ~S" name)))
                 (list :name name :type type :domain domain :numeric numeric :primitive primitive
                       :index (if numeric offset (mezzano.runtime::location-offset-t location))
                       :byte-offset offset
                       :unbound-helper (intern (format nil "%UNBOUND-~A-~D"
                                                      (symbol-name (getf description :native-class)) position)
                                               (symbol-package (getf description :native-class)))
                       :mask (ash 1 (mod position 32))
                       :bound-offset (mezzano.runtime::location-offset
                                      (mezzano.clos:slot-definition-location bound-slot))))
               into found finally (setf fields found))
         (append (list :header (mezzano.runtime::%make-instance-header layout)
                       :payload-bytes (* 8 (mezzano.internals::layout-heap-size layout)) :fields fields)
                 description))) descriptions))

  (defun install-native-operations (identity descriptions operations type-obligations)
    (let ((layouts (finalize-native-layouts descriptions)))
      (dolist (pair operations)
        (let ((name (first pair)) (operation (second pair)))
          (when (eq operation :read)
            (setf (compiler-macro-function (list 'setf name))
                  (lambda (form environment)
                    (declare (ignore environment))
                    (multiple-value-bind (args validp)
                        (snowgrave.mezzano-access::access-call-arguments form (list 'setf name))
                      (unless validp (error "Unknown native record writer call shape."))
                      (expand-record-operation :write
                        (list (second args) (third args) (first args) (fourth args)) layouts)))))
          (setf (compiler-macro-function name)
                (lambda (form environment)
                  (declare (ignore environment))
                  (multiple-value-bind (args validp) (snowgrave.mezzano-access::access-call-arguments form name)
                    (unless validp (error "Unknown native record ABI call shape."))
                    (expand-record-operation operation args layouts))))))
      (setf (gethash identity *native-unit-layouts*)
            (list :layouts layouts :type-obligations type-obligations))))

  (defmacro define-finalized-operations (identity descriptions operations type-obligations)
    (let ((layouts (finalize-native-layouts descriptions)) (record (gensym "RECORD")))
      `(progn
         ;; Isolate the allocating condition/restart environment in the error
         ;; arm. Native closure conversion otherwise captures RECORD at every
         ;; successful read, even though only the unbound branch uses it.
         ,@(loop for layout in layouts append
                 (loop for field in (getf layout :fields)
                       collect `(defun ,(getf field :unbound-helper) (,record)
                                  (restart-case
                                      (error 'unbound-slot :instance ,record :name ',(getf field :name))
                                    (use-value (value) value)
                                    (store-value (value) ,(field-operation :write record 'value field))))))
         (eval-when (:compile-toplevel :load-toplevel :execute)
           (install-native-operations ',identity ',descriptions ',operations ',type-obligations)))))

  (defun native-unit-layouts (identity)
    "Cold layout evidence, including real byte offsets/header and logical CPL."
    (copy-tree (getf (or (gethash identity *native-unit-layouts*) (error "No native unit ~S" identity)) :layouts)))

  (defun admit-supervisor-unit (identity)
    ;; Honest separation: these forms preserve ordinary allocating conditions
    ;; and cold constructors. Success-only execution is not closure admission.
    (let ((unit (or (gethash identity *native-unit-layouts*) (error "No materialized unit ~S" identity))))
      (error "Supervisor admission refused: native TYPEP semantics for ~S, ordinary condition/restart, constructor, code/data residence and full reachable graph ABIs remain required."
             (getf unit :type-obligations))))

  (defmacro define-materialized-unit (metadata forms area)
    (let* ((identity (getf metadata :identity))
           (package (symbol-package (cadr (find 'defun forms :key #'car))))
           (descriptions nil) (definitions nil) (layout-vars nil)
           (generic-bindings
             (loop for binding in (getf metadata :native-generic-bindings) for i from 0
                   collect (list (getf binding :code-name)
                                 (getf binding :code-name)
                                 (intern (format nil "%LOGICAL-GENERIC-OWNER-~D" i) package)
                                 (getf binding :lambda-list) (getf binding :generic)
                                 (intern (format nil "%GENERIC-BODY-~D" i) package))))
           (operations (loop for (host op) in '((snowgrave::%record-read :read) (snowgrave::%record-write :write)
                                               (snowgrave::%record-boundp :boundp) (snowgrave::%record-unbind :unbind)
                                               (snowgrave:sg-record-class :class) (snowgrave:sg-record-p :p)
                                               (snowgrave:sg-record-typep :typep) (snowgrave:sg-record-unit-p :unitp)
                                               (snowgrave:sg-record-layout-p :layoutp))
                             collect (list (intern (format nil "%NATIVE-~A" op) package) op host))))
      (loop for description in (getf metadata :record-layouts) for ordinal from 0 do
        (let* ((name (intern (format nil "%NATIVE-CLASS-~D" ordinal) package))
               (constructor (intern (format nil "%NATIVE-ALLOCATE-~D" ordinal) package))
               (bound-names (loop for i below (ceiling (length (getf description :slots)) 32)
                                  collect (loop for suffix from 0
                                                for candidate = (intern (format nil "%BOUND-~D-~D-~D" ordinal i suffix) package)
                                                unless (member candidate (getf description :slots)) return candidate))))
          (dolist (type (getf description :slot-types)) (native-slot-domain type))
          (push (append (list :native-class name :constructor constructor :bound-names bound-names) description) descriptions)
          (push `(defstruct (,name :sealed (:area ,area) (:constructor ,constructor ()))
                   ,@(mapcar (lambda (x) `(,x 0 :type (unsigned-byte 32))) bound-names)
                   ,@(loop for slot in (getf description :slots) for type in (getf description :slot-types)
                           for domain = (native-slot-domain type)
                           for numeric = (and (consp domain) (member (car domain) '(unsigned-byte signed-byte)))
                           collect `(,slot ,(cond (numeric 0) ((eq domain 'fixnum) 0)
                                                  ((and (consp domain) (eq (car domain) 'member)) (second domain))
                                                  (t nil))
                                           :type ,(if (and (consp domain) (eq (car domain) 'simple-array))
                                                      `(or null ,type) type)))) definitions)))
      (setf descriptions (nreverse descriptions))
      (dolist (form forms)
        (when (and (eq (car form) 'defparameter) (consp (third form))
                   (eq (car (third form)) 'snowgrave:make-layout))
          (let ((description (admitted-logical-layout (cdr (third form)) descriptions)))
            (push (cons (second form) description) layout-vars))))
      (labels ((walk (form)
                 (cond ((atom form) form)
                       ((eq (car form) 'quote) form)
                       ((eq (car form) 'function)
                        (if (and (consp (second form)) (eq (car (second form)) 'lambda))
                            `(function ,(walk (second form))) form))
                       ((eq (car form) 'defun)
                        `(defun ,(or (sixth (find (second form) generic-bindings :key #'first :test #'equal)) (second form))
                           ,(mapcar #'walk (third form))
                           ,@(mapcar #'walk (cdddr form))))
                       ((and (eq (car form) 'restart-case)
                             (consp (second form)) (eq (car (second form)) 'error)
                             (let ((condition (second (second (second form)))))
                               (and (symbolp condition) (symbol-package condition)
                                    (string= (package-name (symbol-package condition)) "SB-PCL")
                                    (string= (symbol-name condition) "NO-APPLICABLE-METHOD-ERROR"))))
                        ;; Actual target ordinary miss protocol, including its
                        ;; CONTINUE retry, receives a real cold-owned native GF.
                        ;; Its body is the SAME emitted CEM, installed once cold.
                        (let* ((error-form (second form))
                               (code-name (second (getf (cddr error-form) :generic-function)))
                               (binding (find code-name generic-bindings :key #'first :test #'equal)))
                          (unless binding (error "No native generic identity for miss."))
                          `(apply #'no-applicable-method ,(third binding)
                                  ,(walk (getf (cddr error-form) :args)))))
                       ((eq (car form) 'snowgrave:sg-record-matches-layout-p)
                        (let ((description (and (= (length form) 3)
                                                (cdr (assoc (third form) layout-vars)))))
                          (unless description (error "Dynamic native admitted-layout proof."))
                          ;; The descriptor was validated cold against the
                          ;; complete metadata row. Reuse the existing native
                          ;; layout operation; no hosted descriptor lookup or
                          ;; new runtime protocol reaches the target.
                          `(,(first (find :layoutp operations :key #'second))
                            ,(walk (second form))
                            ',(getf description :identity) ',(getf description :class)
                            ',(getf description :ancestors) ',(getf description :slots)
                            :slot-types ',(getf description :slot-types)
                            :error-mapping ',(getf description :error-mapping))))
                       ((eq (car form) 'snowgrave:sg-make-record)
                        (let ((description (cdr (assoc (second form) layout-vars))))
                          (unless description (error "Dynamic native constructor layout."))
                          `(,(getf description :constructor))))
                       ((and (eq (car form) 'defparameter) (assoc (second form) layout-vars)) nil)
                       ((eq (car form) 'setf)
                        `(setf ,@(loop for (place value) on (cdr form) by #'cddr
                                       append (list (if (and (consp place) (eq (car place) 'snowgrave::%record-read))
                                                       (cons (first (find :read operations :key #'second)) (mapcar #'walk (cdr place)))
                                                       (walk place)) (walk value)))))
                       (t (cons (if (consp (car form)) (walk (car form))
                                    (or (first (find (car form) operations :key #'third)) (car form)))
                                (mapcar #'walk (cdr form)))))))
        `(progn
           ,@(nreverse definitions)
           ,@(loop for (code name owner lambda-list logical-name kernel) in generic-bindings
                   collect `(defgeneric ,name ,lambda-list)
                   collect `(defparameter ,owner (function ,name)))
           (define-finalized-operations ,identity ,descriptions ,operations ,(getf metadata :native-type-obligations))
           ;; Literal slot names/classes are compile-time proofs, never runtime
           ;; dispatch tables. Original method calls, qualifiers and CEM remain.
           ,@(loop for form in forms for result = (walk form) when result collect result)
           ,@(loop for (code name owner lambda-list logical-name kernel) in generic-bindings
                   collect `(eval-when (:load-toplevel :execute)
                              (reinitialize-instance ,owner :name ',logical-name)
                              (mezzano.clos:set-funcallable-instance-function ,owner (function ,kernel))))))))
)
