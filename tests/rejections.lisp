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

(defun admission-boundary-tests ()
  (dolist (case '(("(eval '(+ 1 2))" :open-operation)
                  ("(funcall #'eval '(+ 1 2))" :indirect-open-operation)
                  ("(mapcar 'eval '((+ 1 2)))" :indirect-open-operation)))
    (let ((feature
            (handler-case
                (progn
                  (make-fixture :admission-boundary
                                (format nil "((defun entry () ~A))" (first case))
                                "(entry)" "((entry ()))" "()")
                  nil)
              (snowgrave:snowgrave-error (condition) (snowgrave:error-feature condition)))))
      (check (eq (second case) feature) "Wrong admission feature for ~A: ~S" (first case) feature)))
  ;; Operation policies match symbol identity, including the source package's shadows.
  (multiple-value-bind (unit package)
      (make-fixture :owned-namesakes
                    "((defun eval (n) (+ n 1))
                       (defun print (n) (+ n 2))
                       (defun entry (n) (values (eval n) (funcall #'print n))))"
                    "(entry)" "((entry (integer)))" "()" :shadows '("EVAL" "PRINT"))
    (compare-entry unit package "ENTRY" '(7) '((8 9) nil))
    (check (equal '(8 9) (multiple-value-list
                         (funcall (snowgrave:bind-entry unit (find-symbol "ENTRY" package) '(7)))))
           "Owned namesakes were mistaken for ambient operations")))
