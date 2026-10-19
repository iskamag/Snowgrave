(in-package #:snowgrave.tests)

(defun slot-place-normalization-tests ()
  (dolist (policy '(:selected :entries))
    (let* ((forms (deployment-forms
                   "((defclass place-cell () ((payload :initarg :payload :initform 17)))
                      (defparameter *place-events* nil)
                      (defun entry ()
                        (setf *place-events* nil)
                        (let ((a (make-instance 'place-cell :payload 17))
                              (b (make-instance 'place-cell :payload 23))
                              (c (make-instance 'place-cell :payload 29)))
                          (let ((rotation
                                  (rotatef (slot-value (progn (push :a *place-events*) a) 'payload)
                                           (slot-value (progn (push :b *place-events*) b) 'payload)
                                           (slot-value (progn (push :c *place-events*) c) 'payload))))
                            (values rotation (slot-value a 'payload) (slot-value b 'payload)
                                    (slot-value c 'payload) (reverse *place-events*))))))"))
           (unit (close-deployment forms :policy policy :classes '(snowgrave.deployment.fixture::place-cell))))
      (check-deployment-parity unit forms '(nil 23 29 17 (:a :b :c))))
    (let* ((forms (deployment-forms
                   "((defclass place-cell () ((payload :initarg :payload :initform 17)))
                      (defparameter *place-events* nil)
                      (defun entry ()
                        (setf *place-events* nil)
                        (let ((a (make-instance 'place-cell :payload 17))
                              (b (make-instance 'place-cell :payload 23)))
                          (let ((old (shiftf (slot-value (progn (push :a *place-events*) a) 'payload)
                                            (slot-value (progn (push :b *place-events*) b) 'payload)
                                            (progn (push :value *place-events*) (values 41 :ignored)))))
                            (values old (slot-value a 'payload) (slot-value b 'payload)
                                    (reverse *place-events*))))))"))
           (unit (close-deployment forms :policy policy :classes '(snowgrave.deployment.fixture::place-cell))))
      (check-deployment-parity unit forms '(17 23 41 (:a :b :value)))))
  ;; Host expansion still feeds the closed success/error slot proof. This
  ;; normalization is not a new dynamic slot dispatcher or native setter ABI.
  (deployment-refusal
   (deployment-forms
    "((defclass place-cell () ((payload :initform 17)))
       (defun entry (name) (let ((object (make-instance 'place-cell)))
                            (rotatef (slot-value object name) (slot-value object 'payload)))))")
   :dynamic-slot :classes '(snowgrave.deployment.fixture::place-cell) :domains '(symbol))
  (deployment-refusal
   (deployment-forms "((defun entry () (sb-pcl::set-slot-value nil)))")
   :host-slot-setter-shape)
  t)
