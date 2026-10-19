(in-package #:snowgrave.tests)

(defun open-host-operation-tests ()
  ;; Full-source syntax is compiled in the disposable world even when its
  ;; ordinary helper is proved absent from the deployed entry closure.
  (dolist (spec '(("(slot-value object name)" :dynamic-slot)
                  ("(slot-boundp object name)" :dynamic-slot)
                  ("(slot-makunbound object name)" :dynamic-slot)
                  ("(setf (slot-value object name) value)" :dynamic-slot-writer)))
    (let* ((forms (deployment-forms
                   (format nil "((defun cold (object name &optional value)
                                   (declare (ignorable object name value)) ~A)
                                 (defun entry () 17))" (first spec))))
           (unit (close-deployment forms)))
      (check-deployment-parity unit forms '(17))
      (check (not (deployment-retained-p unit 'snowgrave.deployment.fixture::cold)))
      (signals error (snowgrave:unit-function unit 'snowgrave.deployment.fixture::cold))
      (deployment-refusal forms (second spec) :policy :selected)
      ;; A call, escaping callable or published callable keeps this helper;
      ;; closed dynamic slot dispatch is still outside this adapter profile.
      (dolist (tail '("(defun entry () (cold nil 'payload 23))"
                      "(defun entry () #'cold)"
                      "(defparameter *saved* #'cold) (defun entry () 17)"))
        (deployment-refusal
         (deployment-forms
          (format nil "((defun cold (object name &optional value)
                           (declare (ignorable object name value)) ~A) ~A)" (first spec) tail))
         (second spec)))))
  (let* ((forms (deployment-forms
                 "((defclass node () ((payload :initarg :payload)))
                    (defun cold (class name value)
                      (make-instance class name value))
                    (defun entry () 17))"))
         (unit (close-deployment forms :classes '(snowgrave.deployment.fixture::node))))
    (check-deployment-parity unit forms '(17))
    (check (not (deployment-retained-p unit 'snowgrave.deployment.fixture::cold)))
    (deployment-fresh-test unit '(17))
    (deployment-refusal forms :dynamic-construction-class :policy :selected
                        :classes '(snowgrave.deployment.fixture::node)))
  (dolist (tail '("(defun entry () (cold 'node :payload 17))"
                  "(defun entry () #'cold)"
                  "(defparameter *saved* #'cold) (defun entry () 17)"))
    (deployment-refusal
     (deployment-forms
      (format nil "((defclass node () ((payload :initarg :payload)))
                     (defun cold (class name value) (make-instance class name value)) ~A)" tail))
     :dynamic-construction-class :classes '(snowgrave.deployment.fixture::node)))
  ;; Constant class construction with unknown keyword syntax likewise needs
  ;; an actual closed tuple proof, rather than borrowing the OPEN allowance.
  (let* ((forms (deployment-forms
                 "((defclass node () ((payload :initarg :payload)))
                    (defun cold (name value) (make-instance 'node name value))
                    (defun entry () 17))"))
         (unit (close-deployment forms :classes '(snowgrave.deployment.fixture::node))))
    (check-deployment-parity unit forms '(17))
    (deployment-refusal
     (deployment-forms
      "((defclass node () ((payload :initarg :payload)))
         (defun cold (name value) (make-instance 'node name value))
         (defun entry () (cold :payload 17)))")
     :construction-initargs :classes '(snowgrave.deployment.fixture::node)))
  t)
