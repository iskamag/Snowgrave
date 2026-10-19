(in-package #:snowgrave.tests)

(defvar *callable-payload-sequence* 0)
(defun callable-payload-choice () t)
(defun callable-payload-native (value) (declare (ignore value)) 23)
(defun callable-payload-publish (value) (declare (ignore value)) 0)

(defun callable-payload-case (tag body &key (type "(unsigned-byte 17)")
                                          (policy :entries) refusal expected native-datum
                                          extra (slot-options "") (class-options "")
                                          (operation "(defun operation (value) (declare (ignore value)) 17)")
                                          writer private-container)
  ;; Invalid typed stores have undefined ANSI source behavior. Such cases
  ;; assert admission refusal, never native error parity. Accepted native
  ;; target errors instead verify the closed datum's exact unchanged identity.
  (let* ((index (incf *callable-payload-sequence*))
         (package (make-package (format nil "SNOWGRAVE.CALLABLE.PAYLOAD.~D" index) :use '("CL")))
         (*package* package)
         (forms (read-from-string
                 (format nil "((defclass holder () ((data :type ~A :initarg :data ~A)
                                                     (out :initarg :out) (inventory :initarg :inventory)) ~A)
                               ~A ~A (defun entry (object) (declare (ignorable object)) ~A))"
                         type slot-options class-options operation (or extra "") body)))
         (holder (intern "HOLDER" package)) (entry (intern "ENTRY" package))
         (generics (remove-duplicates
                    (append (when writer (list (intern writer package)))
                            (loop for form in forms when (member (car form) '(defgeneric defmethod))
                                  collect (second form))) :test #'equal)))
    (dolist (form forms) (eval form))
    (let* ((array (vector nil))
           (root (make-instance holder :data 17 :out array :inventory nil))
           (native-root (make-instance holder :data 17 :out (vector nil) :inventory nil))
           (unit nil)
           (condition
             (handler-case
                 (progn
                   (when private-container (setf (slot-value root (intern "INVENTORY" package)) (vector root)))
                   (setf unit (snowgrave:close-source-unit
                               (list :forms forms) :unit-name (list :callable-payload tag index)
                               :deployment-roots policy :closed-classes (list holder) :closed-generics generics
                               :universe (list holder t) :entries (list entry)
                               :external-domains (list (list entry (list (list 'eql root))))
                               :external-operations '(callable-payload-choice callable-payload-native callable-payload-publish)
                               :native-bindings (list (list :out array))))
                   nil)
               (snowgrave:snowgrave-error (condition) condition))))
      (cond
        (refusal
         (check (typep condition 'snowgrave:snowgrave-error))
         (unless (eq refusal (snowgrave:error-feature condition))
           (error "~S expected ~S, got ~A" tag refusal condition))
         (check (eq refusal (snowgrave:error-feature condition)))
         (check (not (null (snowgrave:error-source-key condition)))))
        (native-datum
         (check (null condition))
         (let ((error (handler-case (funcall (snowgrave:unit-function unit entry :bind-configuration t))
                        (type-error (condition) condition))))
           (check (typep error 'type-error))
           (check (eq (type-error-datum error) (fdefinition native-datum)))))
        (t
         (check (null condition))
         (check (equal expected (multiple-value-list (funcall entry native-root))))
         (check (equal expected (multiple-value-list
                                 (funcall (snowgrave:unit-function unit entry :bind-configuration t)))))))
      (check (null (aref array 0))))))

(defun callable-payload-tests ()
  (dolist (policy '(:selected :entries))
    (callable-payload-case :store "(setf (slot-value object 'data) #'operation) 17"
      :policy policy :refusal :graph-state-write)
    (callable-payload-case :construction "(make-instance 'holder :data #'operation) 17"
      :policy policy :refusal :construction-private-type-error))
  (dolist (value '("(let ((callback #'operation)) (setf (slot-value object 'data) callback))"
                   "(setf (slot-value object 'data)
                           (if (snowgrave.tests::callable-payload-choice) #'operation #'identity))"
                   "(setf (slot-value object 'data) #'(lambda (value) (declare (ignore value)) 17))"
                   "(flet ((callback (value) (declare (ignore value)) 17))
                      (setf (slot-value object 'data) #'callback))"))
    (callable-payload-case :indirect-store value :refusal :graph-state-write))
  (callable-payload-case :generic-store "(setf (slot-value object 'data) #'operation) 17"
    :operation "(defgeneric operation (value)) (defmethod operation ((value t)) 17)"
    :refusal :graph-state-write)
  (callable-payload-case :generated-writer "(store-data #'operation object) 17"
    :slot-options ":writer store-data" :writer "STORE-DATA" :refusal :graph-state-write)
  (callable-payload-case :initform "(make-instance 'holder) 17" :slot-options ":initform (initial-callback)"
    :extra "(defun initial-callback () #'operation)" :refusal :construction-private-type-error)
  (callable-payload-case :default "(make-instance 'holder) 17"
    :class-options "(:default-initargs :data #'operation)" :refusal :construction-private-type-error)
  (callable-payload-case :ignored-initarg "(make-instance 'holder :ignored #'operation) 17"
    :type "t" :refusal :construction-private-initarg)
  (callable-payload-case :invalid-key "(make-instance 'holder :data #'operation :unknown 0) 17"
    :type "t" :refusal :construction-private-keywords)
  (callable-payload-case :assertion
    "(the fixnum (if (snowgrave.tests::callable-payload-choice) #'operation 17)) 17"
    :refusal :private-type-assertion-error)
  ;; Internal T storage does not itself publish the callable. Required input
  ;; capture auditing remains active, and the actual finite callback still runs.
  (callable-payload-case :valid-store
    "(setf (slot-value object 'data) #'operation) (funcall (slot-value object 'data) 0)"
    :type "t" :expected '(17))
  (callable-payload-case :valid-construction
    "(let ((fresh (make-instance 'holder :data #'operation))) (funcall (slot-value fresh 'data) 0))"
    :type "t" :expected '(17))
  (callable-payload-case :valid-local-store
    "(flet ((callback (value) (declare (ignore value)) 17))
       (setf (slot-value object 'data) #'callback) (typep (slot-value object 'data) 'function))"
    :type "t" :expected '(t))
  (callable-payload-case :valid-lambda-store
    "(setf (slot-value object 'data) #'(lambda (value) (declare (ignore value)) 17))
     (typep (slot-value object 'data) 'function)" :type "t" :expected '(t))
  (callable-payload-case :function-slot "17" :type "function" :refusal :typed-slot)
  ;; A native target keeps the same fcell, including when a different captured
  ;; field holds a private-containing native aggregate. Its TYPE-ERROR datum
  ;; is therefore not relocated private callable authority.
  (callable-payload-case :native-target "(setf (slot-value object 'data) #'identity) 17"
    :native-datum 'identity :private-container t)
  (callable-payload-case :foreign-target
    "(make-instance 'holder :data #'snowgrave.tests::callable-payload-native) 17"
    :native-datum 'callable-payload-native)
  (dolist (pair '(("(setf *published* #'operation) 17" :external-shared-state-representation)
                  ("(setf (aref (slot-value object 'out) 0) #'operation) 17" :graph-state-write)
                  ("(snowgrave.tests::callable-payload-publish #'operation) 17" :graph-state-external-argument)
                  ("(values 17 #'operation)" :graph-state-result)
                  ("(throw :outside #'operation)" :graph-state-throw)))
    (callable-payload-case :boundary (first pair) :type "t" :extra "(defparameter *published* nil)"
      :refusal (second pair)))
  t)
