(in-package #:snowgrave.tests)

(defvar snowgrave.deployment.fixture::*ambient-cold-input* 0)
(defun snowgrave.deployment.fixture::ambient-cold-function () 17)

(defun cold-combination-forms (body &optional helpers (defaults "()"))
  (deployment-forms
   (format nil "((defparameter *cold-count* 0) ~A
     (define-method-combination stable-recipe ~A ((primary () :required t))
       (declare (ignore primary)) ~A)
     (defgeneric cold-run (x) (:method-combination stable-recipe))
     (defmethod cold-run ((x t)) 99) (defun entry () (cold-run 0)))"
           (or helpers "") defaults body)))

(defun cold-method-combination-tests ()
  (dolist (policy '(:selected :entries))
    ;; Every actual factory execution must be a stable recipe. A source
    ;; global is not a one-shot counter for inference/materialization passes.
    (dolist (case '(("(incf *cold-count*)")
                    ("*cold-count*")
                    ("(read-count)" "(defun read-count () *cold-count*)")
                    ("(relay-count)" "(defun relay-count () (change-count)) (defun change-count () (incf *cold-count*))")
                    ("*ambient-cold-input*")
                    ("(ambient-cold-function)")
                    ("(setf (symbol-value '*ambient-cold-input*) 17)")
                    ("(read-ambient)" "(defun read-ambient () *ambient-cold-input*)")
                    ("(funcall #'read-count)" "(defun read-count () *cold-count*)")
                    ("(let ((data '(17))) (setf (car data) 23) (car data))")
                    ("(get-universal-time)")
                    ("(macrolet ((one () '(incf *cold-count*))) (one))")
                    ("'(macrolet ((one () (incf *cold-count*))) (one))")
                    ("17" nil "(&optional (ignored (incf *cold-count*)))")))
      (deployment-refusal (apply #'cold-combination-forms case) :method-combination-recipe
                          :policy policy :generics '(snowgrave.deployment.fixture::cold-run)))
    ;; Registry-dependent construction remains an explicit unsupported cold
    ;; recipe. Refusing this does not implement indirect class-name mapping.
    (deployment-refusal
     (cold-combination-forms "(recipe)"
      "(defclass cold-node () ((payload :initform 17)))
       (defun recipe () (slot-value (funcall #'make-instance 'cold-node) 'payload))")
     :method-combination-recipe :policy policy :classes '(snowgrave.deployment.fixture::cold-node)
     :generics '(snowgrave.deployment.fixture::cold-run))
    ;; Preserve lexical mutation/construction, local callbacks, transitive
    ;; authored helpers and finite source recipes without an effect cache.
    (dolist (case '(("(let ((forms nil)) (push 17 forms) (list 'quote (car forms)))")
                    ("(let ((answer nil)) (setq answer 17) answer)")
                    ("(flet ((literal (x) (list 'quote x))) (cons 'progn (mapcar #'literal '(17))))")
                    ("(recipe 17)" "(defun recipe (value) (literal value)) (defun literal (value) (list 'quote value))")
                    ("(min 17 23)")))
      (let* ((forms (apply #'cold-combination-forms case))
             (unit (close-deployment forms :policy policy :generics '(snowgrave.deployment.fixture::cold-run))))
        (check-deployment-parity unit forms '(17))))
    ;; Quoted runtime code is not an effect of its cold construction. The
    ;; CEM's actual runtime write must still use the ordinary shared owner.
    (let* ((forms (cold-combination-forms "'(incf *cold-count*)"))
           (unit (close-deployment forms :policy policy :generics '(snowgrave.deployment.fixture::cold-run))))
      (dolist (form forms) (eval form))
      (setf (symbol-value 'snowgrave.deployment.fixture::*cold-count*) 0)
      (check (= 1 (funcall 'snowgrave.deployment.fixture::entry)))
      (setf (symbol-value 'snowgrave.deployment.fixture::*cold-count*) 0)
      (check (= 1 (funcall (snowgrave:unit-function unit 'snowgrave.deployment.fixture::entry))))))
  t)
