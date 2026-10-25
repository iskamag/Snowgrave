(in-package #:snowgrave.tests)

(defun rejection-tests ()
  (dolist (source '("((defun entry () (eval '(+ 1 2))))"
                    "((defclass cell () ()) (defun entry () (sxhash (make-instance 'cell))))"
                    "((defclass cell () ())
                       (defun entry ()
                         (let ((object (make-instance 'cell))) (funcall #'sxhash object))))"
                    "((defun entry () (snowgrave.tests::note-event :undeclared)))"))
    (check-signals (snowgrave:snowgrave-error)
      (make-fixture :rejection source "(entry)" "((entry ()))" "()")
      "Unsupported source was admitted: ~A" source))
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
    (check-signals (snowgrave:snowgrave-error :physical-type)
      (make-fixture :metadata-type-refusal
                    (format nil "((defclass sample () ((value :initform nil)))
                                  (defun entry () ~A))" observation)
                    "(entry)" "((entry ()))" "()")
      "Metadata observation ~A needs physical-type refusal" observation))
  (dolist (type '(standard-class (or null standard-class)))
    (check-signals (snowgrave:snowgrave-error :slot-type)
      (make-fixture :metadata-slot-refusal
                    (format nil "((defclass holder () ((class :initarg :class :type ~S)))
                                  (defun entry () (make-instance 'holder :class nil)))" type)
                    "(entry)" "((entry ()))" "()")
      "Physical metadata slot type ~S was admitted" type))
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
    (check-signals (snowgrave:snowgrave-error (third case))
      (make-fixture :partition-refusal (first case) "(entry)" "((entry (t)))"
                    "(classify)" :universe (second case))
      "Wrong partition refusal"))
  (check-signals (snowgrave:snowgrave-error)
    (snowgrave:close-source-unit '(:forms ((defun unsupported-entry () 7)))
                                 :unit-name (list :unsupported-configuration (incf *fixture-sequence*))
                                 :entries '(unsupported-entry) :external-domains '((unsupported-entry ()))
                                 :native-bindings nil)
    "Removed configuration declaration was silently accepted"))

(defun admission-boundary-tests ()
  (dolist (case '(("(eval '(+ 1 2))" :open-operation)
                  ("(funcall #'eval '(+ 1 2))" :indirect-open-operation)
                  ("(mapcar 'eval '((+ 1 2)))" :indirect-open-operation)))
    (check-signals (snowgrave:snowgrave-error (second case))
      (make-fixture :admission-boundary
                    (format nil "((defun entry () ~A))" (first case))
                    "(entry)" "((entry ()))" "()")
      "Wrong admission feature for ~A" (first case)))
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
