(in-package #:snowgrave.tests)

(defun rejection-tests ()
  (dolist (source '("((defun entry () (eval '(+ 1 2))))"
                    "((defclass cell () ()) (defun entry () (sxhash (make-instance 'cell))))"
                    "((defclass cell () ())
                       (defun entry ()
                         (let ((object (make-instance 'cell))) (funcall #'sxhash object))))"
                    "((defun entry () (snowgrave.tests::note-event :undeclared)))"))
    (let ((rejected nil))
      (handler-case (make-fixture :rejection source "(entry)" "((entry ()))" "()")
        (snowgrave:snowgrave-error () (setf rejected t)))
      (check rejected "Unsupported source was admitted: ~A" source)))
  ;; The metadata queries return logical descriptors. A native TYPEP on their
  ;; physical DEFSTRUCT representation must not silently change a true answer.
  (dolist (observation
           '("(typep (find-class 'sample) 'class)"
             "(typep (find-class 'sample) 'standard-class)"
             "(typep (find-class 'sample) 'closer-mop:metaobject)"
             "(typep (first (closer-mop:class-slots (find-class 'sample)))
                      'closer-mop:slot-definition)"
             "(typep (first (closer-mop:class-slots (find-class 'sample)))
                      'closer-mop:standard-effective-slot-definition)"
             "(typep (find-class 'sample) '(or null standard-class))"
             "(the standard-class (find-class 'sample))"
             "(let ((class (find-class 'sample)))
                (declare (type standard-class class)) class)"))
    (let ((feature nil))
      (handler-case
          (make-fixture :metadata-type-refusal
                        (format nil "((defclass sample () ((value :initform nil)))
                                      (defun entry () ~A))" observation)
                        "(entry)" "((entry ()))" "()")
        (snowgrave:snowgrave-error (condition)
          (setf feature (snowgrave:error-feature condition))))
      (check (eq feature :physical-type)
             "Metadata observation ~A needs physical-type refusal, got ~S"
             observation feature)))
  (dolist (type '(standard-class (or null standard-class)))
    (let ((feature nil))
      (handler-case
          (make-fixture :metadata-slot-refusal
                        (format nil "((defclass holder () ((class :initarg :class :type ~S)))
                                      (defun entry () (make-instance 'holder :class nil)))" type)
                        "(entry)" "((entry ()))" "()")
        (snowgrave:snowgrave-error (condition)
          (setf feature (snowgrave:error-feature condition))))
      (check (eq feature :slot-type)
             "Physical metadata slot type ~S was admitted, feature ~S" type feature)))
  (dolist (case '(("((defgeneric classify (x))
                     (defmethod classify ((x array)) :array)
                     (defmethod classify ((x sequence)) :sequence)
                     (defun entry (x) (classify x)))"
                  "(array sequence)" (:native-partition :specializer))
                 ("((defgeneric classify (x))
                     (defmethod classify ((x (eql :one))) :one)
                     (defun entry (x) (classify x)))"
                  "(symbol)" (:eql-specializer))
                 ("((defgeneric classify (x))
                     (defmethod classify ((x number)) x)
                     (defmethod classify ((x integer)) (call-next-method (+ x 1)))
                     (defun entry (x) (classify x)))"
                  "(integer number)" (:changed-next-method))
                 ("((defgeneric classify (x))
                     (defmethod classify ((x number)) x)
                     (defmethod classify ((x integer)) (funcall #'call-next-method))
                     (defun entry (x) (classify x)))"
                  "(integer number)" (:next-method-capture))))
    (let ((feature nil))
      (handler-case
          (make-fixture :partition-refusal (first case) "(entry)" "((entry (t)))"
                        "(classify)" :universe (second case))
        (snowgrave:snowgrave-error (condition)
          (setf feature (snowgrave:error-feature condition))))
      (check (member feature (third case)) "Wrong partition refusal: ~S, expected one of ~S" feature (third case))))
  (let ((rejected nil))
    (handler-case
        (snowgrave:close-source-unit '(:forms ((defun unsupported-entry () 7)))
                                     :unit-name (list :unsupported-configuration (incf *fixture-sequence*))
                                     :entries '(unsupported-entry) :external-domains '((unsupported-entry ()))
                                     :native-bindings nil)
      (snowgrave:snowgrave-error () (setf rejected t)))
    (check rejected "Removed configuration declaration was silently accepted")))
