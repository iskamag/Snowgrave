(defpackage #:snowgrave.required-domains.fixture (:use #:cl))
(in-package #:snowgrave.tests)

(defun required-domain-forms ()
  (let ((*package* (find-package :snowgrave.required-domains.fixture)))
    (read-from-string
     "((defclass marker () ())
       (defgeneric store (data value))
       (defmethod store :around ((data cons) value)
         (observe :enter)
         (multiple-value-prog1 (call-next-method) (observe :exit)))
       (defmethod store :before ((data cons) value) (observe :before))
       (defmethod store :after ((data cons) value) (observe :after))
       (defmethod store ((data cons) value)
         (setf (car data) value) (observe :write) (values value :stored))
       (defun direct (data value) (store data value))
       (defun indirect (data value) (funcall #'store data value))
       (defun via-apply (data value) (apply #'store data (list value)))
       (defun via-values (data value) (multiple-value-call #'store (values data value)))
       (defun via-helper (data value) (store data (later value)))
       (defun later (value) value))")))

(defun close-required-domain-unit (identity &key extra-forms extra-domains only-entry)
  (let* ((*package* (find-package :snowgrave.required-domains.fixture))
         (forms (append (required-domain-forms) extra-forms)))
    (snowgrave:close-source-unit
     (list :forms forms) :unit-name identity
     :closed-classes (list (intern "MARKER"))
     :closed-generics (loop for form in forms when (eq (car form) 'defgeneric) collect (second form))
     :universe (list (intern "MARKER") 'cons 'number 'integer 'function)
     :entries (if only-entry (mapcar #'first extra-domains)
                  (append (mapcar #'intern '("DIRECT" "INDIRECT" "VIA-APPLY" "VIA-VALUES" "VIA-HELPER"))
                          (mapcar #'first extra-domains)))
     :external-domains
     (append (unless only-entry
               (mapcar (lambda (name) (list (intern name) '(cons integer)))
                       '("DIRECT" "INDIRECT" "VIA-APPLY" "VIA-VALUES" "VIA-HELPER")))
             extra-domains)
     :external-operations (list (intern "OBSERVE")))))

(defun required-domain-fresh-test (unit)
  (let ((script (merge-pathnames "scripts/fresh-required-domains.lisp"
                                (asdf:system-source-directory "snowgrave"))))
    (uiop:with-temporary-file (:stream output :pathname source :type "lisp" :direction :output)
      (uiop:with-temporary-file (:stream meta-output :pathname metadata :type "metadata" :direction :output)
        (snowgrave:write-unit-source unit output)
        (snowgrave:write-unit-metadata unit meta-output)
        (finish-output output) (finish-output meta-output)
        (unwind-protect
             (check (search "Fresh required generic domains executed."
                            (uiop:run-program
                             (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                                   (namestring script) (namestring source) (namestring metadata))
                             :output :string)))
          (ignore-errors (delete-file (compile-file-pathname source))))))))

(defun generic-required-domain-tests ()
  (let* ((*package* (find-package :snowgrave.required-domains.fixture))
         (cell (intern "*CELL*")) (events (intern "*EVENTS*")))
    ;; This owner can already observe the argument's cons by an external alias.
    ;; No private-aggregate claim or representation-changing store is admitted.
    (eval `(defparameter ,cell nil))
    (eval `(defparameter ,events nil))
    (eval (read-from-string
           "(defun observe (phase) (push (list phase (car *cell*)) *events*) nil)"))
    (let* ((unit (close-required-domain-unit '(:required-generic-domains)))
           (metadata (snowgrave:unit-metadata unit)))
      (dolist (form (required-domain-forms)) (eval form))
      (dolist (name '("DIRECT" "INDIRECT" "VIA-APPLY" "VIA-VALUES" "VIA-HELPER"))
        (dolist (value '(0 37 -29))
          (labels ((observe-call (function)
                     (setf (symbol-value cell) (cons nil nil) (symbol-value events) nil)
                     (list (multiple-value-list (funcall function (symbol-value cell) value))
                           (copy-tree (reverse (symbol-value events))) (car (symbol-value cell)))))
            (let ((expected (observe-call (fdefinition (intern name))))
                  (actual (observe-call (test-unit-function unit name))))
              (check (equal expected actual))
              (check (equal actual
                            (list (list value :stored)
                                  (list '(:enter nil) '(:before nil) (list :write value)
                                        (list :after value) (list :exit value)) value)))))))
      ;; Caller evidence now covers required-only generics as well as keys.
      (let* ((flow (getf metadata :ordinary-function-flow))
             (rows (getf flow :generic-call-bindings))
             (row (find "STORE" rows :key (lambda (row) (second (getf row :generic-key))) :test #'equal)))
        (check (getf row :raw-call-shapes)))
      (required-domain-fresh-test unit))
    ;; Each additional reachable caller invalidates the narrower numeric proof.
    ;; An escaping function or unknown APPLY tail cannot borrow DIRECT's input.
    (loop for (source domains feature) in
      '(("(defun broad (data value) (store data value))" "((broad (cons t)))"
         :external-shared-state-representation)
        ("(defun capture () #'store)" "((capture ()))" :external-shared-state-representation)
        ("(defun tail-call (data tail) (apply #'store data tail))" "((tail-call (cons t)))" :apply-arguments)
        ("(defun all-tail (tail) (apply #'store tail))" "((all-tail (t)))" :apply-arguments)
        ("(defun record-value (data value) (store data value))" "((record-value (cons marker)))"
         :external-shared-state-representation)
        ("(defun callable-value (data) (store data #'observe))" "((callable-value (cons)))"
         :external-shared-state-representation)
        ("(defun broad-values (data value) (multiple-value-call #'store (values data) (values value)))"
         "((broad-values (cons marker)))" :external-shared-state-representation)
        ("(defun broad-helper (data value) (store data (later value)))"
         "((broad-helper (cons marker)))" :external-shared-state-representation))
      for index from 1 do
      (let ((condition
              (handler-case
                  (progn (close-required-domain-unit
                          (list :required-generic-domain-refusal index)
                          :extra-forms (list (read-from-string source))
                          :extra-domains (read-from-string domains)) nil)
                (snowgrave:snowgrave-error (condition) condition))))
        (check (typep condition 'snowgrave:snowgrave-error))
        (check (eq feature (snowgrave:error-feature condition)))))
    ;; Required facts and return facts share the same monotone fixed point.
    ;; A recursive universal argument must converge without becoming T, but a
    ;; later record-valued entry must still widen that same recursive proof.
    (let ((forms (read-from-string
                  "((defgeneric bounce (value n))
                    (defmethod bounce (value (n integer))
                      (if (zerop n) value (bounce value (1- n))))
                    (defun recursive (data value n) (store data (bounce value n))))")))
      (let ((unit (close-required-domain-unit
                   '(:recursive-required-generic) :extra-forms forms
                   :extra-domains (read-from-string "((recursive (cons integer integer)))"))))
        (dolist (form forms) (eval form))
        (dolist (n '(0 1 7))
          (setf (symbol-value cell) (list nil) (symbol-value events) nil)
          (let ((expected (multiple-value-list (funcall (intern "RECURSIVE") (symbol-value cell) 71 n)))
                (trace nil))
            (setf trace (reverse (symbol-value events))
                  (symbol-value cell) (list nil) (symbol-value events) nil)
            (check (equal expected (multiple-value-list
                                    (funcall (test-unit-function unit "RECURSIVE") (symbol-value cell) 71 n))))
            (check (equal trace (reverse (symbol-value events))))
            (check (= 71 (car (symbol-value cell)))))))
      (let ((condition
              (handler-case
                  (progn (close-required-domain-unit
                          '(:recursive-required-generic-refusal) :extra-forms forms
                          :extra-domains (read-from-string "((recursive (cons marker integer)))")) nil)
                (snowgrave:snowgrave-error (condition) condition))))
        (check (typep condition 'snowgrave:snowgrave-error))
        (check (eq :external-shared-state-representation (snowgrave:error-feature condition)))))
    ;; No source caller is not proof that all selected method code is dead.
    (let ((condition
            (handler-case
                (progn (close-required-domain-unit
                        '(:unreached-required-generic)
                        :extra-forms (list (read-from-string "(defun entry () 7)"))
                        :extra-domains (read-from-string "((entry ()))") :only-entry t) nil)
              (snowgrave:snowgrave-error (condition) condition))))
      (check (typep condition 'snowgrave:snowgrave-error))
      (check (eq :external-shared-state-representation (snowgrave:error-feature condition))))
    ;; An uncalled helper is outside the deployment cohort. Its unconstrained
    ;; LENGTH must not poison facts from the actual entry-reachable callers.
    (let* ((forms (read-from-string
                   "((defclass marker () ())
                     (defgeneric store (data value))
                     (defmethod store (data value) (setf (car data) value))
                     (defun entry (data) (store data 17))
                     (defun unused (data value) (store data (length value))))"))
           (unit (snowgrave:close-source-unit
                  (list :forms forms) :unit-name '(:unused-required-generic-caller)
                  :closed-classes (list (intern "MARKER")) :closed-generics (list (intern "STORE"))
                  :universe (list (intern "MARKER") 'cons 't) :entries (list (intern "ENTRY"))
                  :external-domains (list (list (intern "ENTRY") '(cons)))
                  :external-operations (list (intern "OBSERVE"))))
           (data (list nil)))
      (check (= 17 (funcall (test-unit-function unit "ENTRY") data)))
      (check (= 17 (car data)))
      (signals error (snowgrave:unit-function unit "UNUSED")))))
