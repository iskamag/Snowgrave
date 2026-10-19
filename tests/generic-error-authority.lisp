(in-package #:snowgrave.tests)

(defvar *generic-error-authority-sequence* 0)

(defun generic-error-authority-callables (condition)
  ;; Test the actual native condition payload, rather than assuming that an
  ;; error class implies absence of invocation authority.
  (remove-duplicates
   (loop for slot in (sb-mop:class-slots (class-of condition))
         for name = (sb-mop:slot-definition-name slot)
         when (slot-boundp condition name)
           append (let ((value (slot-value condition name)))
                    (cond ((functionp value) (list value))
                          ((listp value) (remove-if-not #'functionp value)))))
   :test #'eq))

(defun generic-error-authority-case (tag body &key
                                          (policy :entries) (configured t)
                                          (methods "(defmethod operation ((value t))
                                                       (declare (ignore value))
                                                       (make-instance 'authority-holder :data 23))")
                                          (extra "") (generics "operation")
                                          refusal expected native-error private-result)
  (let* ((index (incf *generic-error-authority-sequence*))
         (package (make-package (format nil "SNOWGRAVE.GENERIC.AUTHORITY.~D" index) :use '("CL")))
         (*package* package)
         (forms (read-from-string
                 (format nil "((defclass authority-holder () ((data :initarg :data) (arguments :initarg :arguments)))
                               (defgeneric operation (value)) ~A ~A
                               (defun entry (root) (declare (ignorable root)) ~A))"
                         methods extra body)))
         (holder (intern "AUTHORITY-HOLDER" package))
         (operation (intern "OPERATION" package)) (entry (intern "ENTRY" package))
         (closed-generics (read-from-string (format nil "(~A)" generics)))
         (unit nil) (failure nil) (native nil))
    (dolist (form forms) (eval form))
    (flet ((make-root ()
             (let ((record (allocate-instance (find-class holder))))
               (setf (slot-value record (intern "DATA" package)) 17
                     (slot-value record (intern "ARGUMENTS" package)) nil)
               record)))
     (let ((native-root (make-root)) (closed-root (make-root)))
      (setf native (handler-case (multiple-value-list (funcall entry native-root))
                     (error (condition) condition)))
      (if native-error
          (progn
            (check (typep native 'error))
            (check (member (fdefinition (if (eq native-error t) operation native-error))
                           (generic-error-authority-callables native) :test #'eq))
            (when private-result
              ;; A defined native call through the condition's callable may
              ;; return a private-class instance. Unknown input auditing alone
              ;; cannot establish the relocated callable's public result ABI.
              (check (typep (funcall (fdefinition operation) 0) holder))))
          (check (equal expected native)))
      (handler-case
          (setf unit (snowgrave:close-source-unit
                      (list :forms forms) :unit-name (list :generic-error-authority tag index)
                      :deployment-roots policy :closed-classes (list holder)
                      :closed-generics closed-generics :universe (list holder 'number t)
                      :entries (list entry)
                      :external-domains (list (list entry (list (if configured (list 'eql closed-root) t))))))
        (snowgrave:snowgrave-error (condition) (setf failure condition)))
      (cond
        (refusal
         (check (typep failure 'snowgrave:snowgrave-error))
         (unless (eq refusal (snowgrave:error-feature failure))
           (error "~S expected ~S, got ~A" tag refusal failure))
         (check (eq refusal (snowgrave:error-feature failure)))
         (check (not (null (snowgrave:error-source-key failure)))))
        (native-error
         ;; General unconfigured units retain the ordinary error mapping.
         (check (null failure))
         (let ((closed (handler-case (funcall (snowgrave:unit-function unit entry) closed-root)
                         (error (condition) condition))))
           (check (eq (type-of native) (type-of closed)))
           (check (not (null (generic-error-authority-callables closed))))))
        (t
         (check (null failure))
         (check (equal expected
                       (multiple-value-list
                        (if configured
                            (funcall (snowgrave:unit-function unit entry :bind-configuration t))
                            (funcall (snowgrave:unit-function unit entry) closed-root)))))
         ;; No missing cells were removed to obtain the accepted proof.
         (check (some (lambda (description)
                        (some (lambda (cell) (eq (getf cell :behavior) :standard-no-applicable-method))
                              (getf description :cells)))
                      (getf (snowgrave:unit-metadata unit) :dispatch)))))))))

(defun generic-error-authority-tests ()
  (dolist (policy '(:selected :entries))
    (dolist (body '("(operation) 17"
                    "(funcall #'operation) 17"))
      (generic-error-authority-case :short body :policy policy
        :refusal :graph-state-generic-authority :native-error t :private-result t))
    ;; The shared APPLY binder already excludes this uncertain short tuple.
    (generic-error-authority-case :unknown-tail
      "(apply #'operation (slot-value root 'arguments)) 17" :policy policy
      :refusal :apply-arguments :native-error t :private-result t)
    (generic-error-authority-case :miss "(operation :missing) 17" :policy policy
      :methods "(defmethod operation ((value number))
                   (declare (ignore value)) (make-instance 'authority-holder :data 23))"
      :refusal :graph-state-generic-authority :native-error t :private-result t)
    (generic-error-authority-case :next "(operation :missing) 17" :policy policy
      :methods "(defmethod operation ((value t))
                   (if (eq value :missing) (call-next-method)
                       (make-instance 'authority-holder :data 23)))"
      :refusal :graph-state-generic-authority :native-error t :private-result t)
    (generic-error-authority-case :ordinary-positive "(operation 0)" :policy policy
      :methods "(defmethod operation ((value number)) (declare (ignore value)) 17)"
      :expected '(17))
    (generic-error-authority-case :private-positive "(operation root)" :policy policy
      :methods "(defmethod operation ((value authority-holder)) (declare (ignore value)) 17)"
      :expected '(17)))
  ;; A retained initializer root phase is not an actual constructor-call
  ;; receipt. Conservatively reject its miss rather than borrowing a caller.
  (generic-error-authority-case :initializer-miss
    "(make-instance 'authority-holder :data 17) 17"
    :methods "(defmethod operation ((value t)) (declare (ignore value)) 17)"
    :extra "(defmethod initialize-instance :after ((value authority-holder) &rest initargs)
                 (declare (ignore initargs)) (call-next-method))"
    :generics "operation initialize-instance shared-initialize"
    :refusal :graph-state-generic-authority :native-error 'initialize-instance)
  ;; The unconfigured native-shaped schema remains available. This repair
  ;; does not globally remove native arity/miss behavior or any MOP cell.
  (generic-error-authority-case :general-arity "(operation) 17" :configured nil
    :methods "(defmethod operation ((value t)) (declare (ignore value)) 17)"
    :native-error t)
  t)
