(defpackage #:snowgrave.selected-method-roots.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass #:defgeneric #:defmethod))
(in-package #:snowgrave.tests)
(defun snowgrave.selected-method-roots.fixture::observe () nil)

(defun selected-method-root-tests ()
  (let ((*package* (find-package :snowgrave.selected-method-roots.fixture)))
    (dolist (result '("value" "17"))
      (let* ((forms (read-from-string
                     (format nil "((defun helper (value) ~A)
                                   (defgeneric selected (value))
                                   (defmethod selected (value) (helper value))
                                   (defun entry () 0))" result)))
             (entry (intern "ENTRY")) (helper (intern "HELPER")) (selected (intern "SELECTED"))
             (unit (snowgrave:close-source-unit
                    (list :forms forms) :unit-name (list 'selected-method-helper result)
                    :closed-generics (list selected) :universe '(number t)
                    :entries (list entry) :external-domains (list (list entry nil)))))
        (dolist (form forms) (eval form))
        (check (zerop (funcall (snowgrave:unit-function unit entry))))
        (check (functionp (test-code-function unit helper)))
        (check (handler-case (progn (snowgrave:unit-function unit helper) nil) (error () t)))
        (dolist (value (list 23 :native (vector 1 2)))
          (check (eq (funcall selected value) (funcall (test-code-function unit selected) value))))
        ;; The helper's newly found scalar return must propagate before an
        ;; uncalled selected GF's pending return is irreversibly widened.
        (when (string= result "17")
          (let* ((returns (getf (getf (snowgrave:unit-report unit) :ordinary-function-flow) :generic-returns))
                 (row (find (snowgrave::function-name-key selected) returns
                            :key (lambda (entry) (getf entry :generic-key)) :test #'equal))
                 (domain (getf row :primary-return-domain)))
            (check (and (not (member domain '(:pending :unknown))) (subtypep domain 'integer)))))))
    ;; A helper discovered from an otherwise uncalled selected method still
    ;; contributes its actual tuple to an existing generic's caller proof.
    ;; The real entry's NUMBER tuple cannot hide this later unknown writer.
    (let* ((identity '(selected-method-hidden-writer))
           (forms (read-from-string
                   "((defclass holder () ())
                     (defgeneric store (target value))
                     (defmethod store (target value) (setf (svref target 0) value))
                     (defun relay (target value) (store target value))
                     (defgeneric hidden (value))
                     (defmethod hidden (value) (relay (vector nil) value))
                     (defun entry (target) (store target 17)))"))
           (condition
             (handler-case
                 (progn
                   (snowgrave:close-source-unit
                    (list :forms forms) :unit-name identity
                    :closed-classes (list (intern "HOLDER"))
                    :closed-generics (mapcar #'intern '("STORE" "HIDDEN"))
                    :universe (read-from-string "(holder vector number t)")
                    :entries (list (intern "ENTRY"))
                    :external-domains (list (list (intern "ENTRY") '(vector)))
                    :external-operations (list (intern "OBSERVE")))
                   nil)
               (snowgrave:snowgrave-error (condition) condition))))
      (check (typep condition 'snowgrave:unclosed-call))
      (check (eq :external-shared-state-representation (snowgrave:error-feature condition)))
      (check (equal (list identity 3) (snowgrave:error-source-key condition))))))
