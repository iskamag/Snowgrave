(defpackage #:snowgrave.result-owners.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass))
(in-package #:snowgrave.tests)
(defvar snowgrave.result-owners.fixture::*observed*)
(defun snowgrave.result-owners.fixture::observe ()
  (svref snowgrave.result-owners.fixture::*observed* 0))
(defun snowgrave.result-owners.fixture::opaque () (list :opaque))

(defun indirect-result-owner-forms (callee syntax &optional opaque)
  (let* ((*package* (find-package :snowgrave.result-owners.fixture))
         (argument "(list (measure nil))")
         (call (ecase syntax
                 (:funcall (format nil "(funcall ~A ~A)" callee argument))
                 (:apply (format nil "(apply ~A (list ~A))" callee argument))
                 (:values (format nil "(multiple-value-call ~A (values ~A))" callee argument)))))
    (read-from-string
     (format nil
      "((defclass marker () ())
        (defparameter *events* nil)
        (defun measure (items)
          (push :measure *events*) ~A)
        (defun other (items)
          (push :other *events*) ~A)
        (defun entry (target flag)
          (setf *events* nil)
          (flet ((measure (ignored)
                   (declare (ignore ignored))
                   (push :local-argument *events*) (make-instance 'marker)))
            (multiple-value-bind (value tag) ~A
              (setf (svref target 0) value)
              (observe)
              (values value tag (reverse *events*))))))"
      (if opaque "(opaque)" "(values (length items) :measure)")
      (if opaque "(opaque)" "(values (1+ (length items)) :other)") call))))

(defun close-indirect-result-owner (forms identity &optional opaque)
  (let ((*package* (find-package :snowgrave.result-owners.fixture)))
    (snowgrave:close-source-unit
     (list :forms forms) :unit-name identity
     :closed-classes (list (intern "MARKER")) :universe (read-from-string "(marker t vector list number)")
     :entries (list (intern "ENTRY"))
     :external-domains (list (list (intern "ENTRY") '(vector t)))
     :external-operations (if opaque (mapcar #'intern '("OBSERVE" "OPAQUE")) (list (intern "OBSERVE"))))))

(defun indirect-result-owner-positive-tests ()
  (let ((*package* (find-package :snowgrave.result-owners.fixture)))
    (loop for callee in
          '("(load-time-value #'measure)"
            "(if flag (load-time-value #'measure) (load-time-value #'other))"
            "(progn (push :callee *events*)
                    (if flag (load-time-value #'measure) (load-time-value #'other)))"
            "(load-time-value #'length)")
          for index from 1 do
      (dolist (syntax '(:funcall :apply :values))
        (let* ((forms (indirect-result-owner-forms callee syntax))
               (unit (close-indirect-result-owner forms (list 'indirect-result-owner index syntax)))
               (entry (intern "ENTRY")))
          (dolist (form forms) (eval form))
          (dolist (flag '(nil t))
            (let* ((native-target (vector :untouched))
                   (closed-target (vector :untouched))
                   (native
                     (let ((snowgrave.result-owners.fixture::*observed* native-target))
                       (multiple-value-list (funcall entry native-target flag))))
                   (closed
                     (let ((snowgrave.result-owners.fixture::*observed* closed-target))
                       (multiple-value-list
                        (funcall (snowgrave:unit-function unit entry) closed-target flag)))))
              (check (and (equal native closed)
                          (= (svref native-target 0) (svref closed-target 0))
                          (member :local-argument (third closed)))))))))))

(defun indirect-result-owner-refusal-tests ()
  (let ((*package* (find-package :snowgrave.result-owners.fixture)))
    ;; The literal lexical MEASURE returns a real record. Qualified global
    ;; callee facts cannot be borrowed by this separate local binding.
    (dolist (syntax '(:funcall :apply :values))
      (let* ((identity (list 'indirect-local-record-result syntax))
             (forms (indirect-result-owner-forms "#'measure" syntax))
             (entry (intern "ENTRY"))
             (target (vector :untouched)))
        (dolist (form forms) (eval form))
        (let ((snowgrave.result-owners.fixture::*observed* target)) (funcall entry target t))
        (check (typep (svref target 0) (intern "MARKER")))
        (let ((condition
                (handler-case (progn (close-indirect-result-owner forms identity) nil)
                  (snowgrave:snowgrave-error (condition) condition))))
          (check (typep condition 'snowgrave:unclosed-call))
          (check (eq :external-shared-state-representation (snowgrave:error-feature condition)))
          (check (equal (list identity 5) (snowgrave:error-source-key condition))))))
    ;; The global helper owner proof must preserve an opaque return origin.
    (dolist (syntax '(:funcall :apply :values))
      (let* ((identity (list 'indirect-opaque-result-owner syntax))
             (forms (indirect-result-owner-forms
                     "(if flag (load-time-value #'measure) (load-time-value #'other))" syntax t))
             (condition
               (handler-case (progn (close-indirect-result-owner forms identity t) nil)
                 (snowgrave:snowgrave-error (condition) condition))))
        (check (typep condition 'snowgrave:unclosed-call))
        (check (eq :external-result-state (snowgrave:error-feature condition)))
        (check (equal (list identity 5) (snowgrave:error-source-key condition)))))))

(defun indirect-result-owner-tests ()
  (indirect-result-owner-positive-tests)
  (indirect-result-owner-refusal-tests)
  (indirect-result-provenance-tests)
  (indirect-result-tuple-provenance-tests)
  (indirect-target-analysis-scaling-tests))

(defun indirect-result-provenance-tests ()
  (let ((*package* (find-package :snowgrave.result-owners.fixture)))
    ;; A qualified global identity helper returns the local argument's actual
    ;; record, not the unrelated global MEASURE's numeric result.
    (dolist (call '("(funcall (load-time-value #'same) (measure nil))"
                    "(apply (load-time-value #'same) (list (measure nil)))"
                    "(multiple-value-call (load-time-value #'same) (values (measure nil)))"
                    "(let ((fn #'same)) (funcall fn 17))"
                    "(funcall (if flag (load-time-value #'same) #'same) 17)"))
      (let* ((forms (read-from-string
                     (format nil
                      "((defclass marker () ())
                        (defun same (value) value)
                        (defun measure (ignored) (declare (ignore ignored)) 7)
                        (defun entry (target flag)
                          (flet ((same (value) (declare (ignore value)) (make-instance 'marker))
                                 (measure (ignored) (declare (ignore ignored)) (make-instance 'marker)))
                            (setf (svref target 0) ~A))))" call)))
             (condition
               (handler-case (progn (close-indirect-result-owner forms (list 'local-result-origin call)) nil)
                 (snowgrave:snowgrave-error (condition) condition))))
        (check (typep condition 'snowgrave:unclosed-call))
        (check (eq :external-shared-state-representation (snowgrave:error-feature condition)))))
    ;; UNKNOWN never absorbs opaque origin when caller facts or conditional
    ;; helper returns are joined. Unsupported standard targets (IDENTITY)
    ;; retain the same input scan; an external callee owns an opaque result.
    (dolist (callee '("(load-time-value #'same)"
                      "(if flag (load-time-value #'same) (load-time-value #'conditional))"
                      "(load-time-value #'identity)"))
      (dolist (syntax '(:funcall :apply :values))
        (let* ((argument "(if flag (opaque) unknown)")
               (call (ecase syntax
                       (:funcall (format nil "(funcall ~A ~A)" callee argument))
                       (:apply (format nil "(apply ~A (list ~A))" callee argument))
                       (:values (format nil "(multiple-value-call ~A (values ~A))" callee argument))))
               (forms (read-from-string
                       (format nil
                        "((defclass marker () ())
                          (defun same (value) value)
                          (defun conditional (value) (if value value (opaque)))
                          (defun entry (target flag unknown)
                            (flet ((same (value) (declare (ignore value)) (make-instance 'marker)))
                              (setf (svref target 0) ~A))))" call)))
               (condition
                 (handler-case
                     (progn
                       (snowgrave:close-source-unit
                        (list :forms forms) :unit-name (list 'mixed-indirect-origin callee syntax)
                        :closed-classes (list (intern "MARKER"))
                        :universe (read-from-string "(marker t vector number list)")
                        :entries (list (intern "ENTRY"))
                        :external-domains (list (list (intern "ENTRY") '(vector t t)))
                        :external-operations (mapcar #'intern '("OBSERVE" "OPAQUE"))) nil)
                   (snowgrave:snowgrave-error (condition) condition))))
          (check (typep condition 'snowgrave:unclosed-call))
          (check (eq :external-result-state (snowgrave:error-feature condition))))))))

(defun indirect-target-analysis-scaling-tests ()
  ;; Count visits across the entire close, including the initial pending
  ;; fixed-point passes. A nested callee must not be reanalysed independently
  ;; by target, return, qualification and opaque-input owners at every level.
  (let ((*package* (find-package :snowgrave.result-owners.fixture))
        (original (fdefinition 'snowgrave.sbcl::value-domain)) (visits 0))
    (unwind-protect
         (progn
           (setf (fdefinition 'snowgrave.sbcl::value-domain)
                 (lambda (build form) (incf visits) (funcall original build form)))
           (dolist (shadowp '(nil t))
             (dolist (depth '(4 8 16 32))
               (let* ((choose (intern "CHOOSE")) (entry (intern "ENTRY"))
                      (callee `(load-time-value (function ,choose))))
                 (dotimes (index depth) (setf callee (list 'funcall callee)))
                 (let ((forms `((defun ,choose () (function ,choose))
                                (defun ,entry ()
                                  ,(if shadowp `(flet ((,choose () :local)) ,callee) callee)))))
                   (setf visits 0)
                   (let* ((unit (snowgrave:close-source-unit
                                 (list :forms forms) :unit-name (list 'nested-result-analysis shadowp depth)
                                 :universe '(t function) :entries (list entry)
                                 :external-domains (list (list entry nil))))
                          (analysis-visits visits))
                     ;; The old recurrence exceeded 770,000/1,490,000 visits
                     ;; already at depth8. Leave room for other bounded passes.
                     (check (<= analysis-visits (* 40 (expt (1+ depth) 2))))
                     (dolist (form forms) (eval form))
                     (let ((native (funcall entry))
                           (closed (funcall (snowgrave:unit-function unit entry))))
                       (check (and (functionp native) (eq native (funcall native))))
                       (check (and (functionp closed) (eq closed (funcall closed)))))))))))
      (setf (fdefinition 'snowgrave.sbcl::value-domain) original))))

(defun indirect-result-tuple-provenance-tests ()
  (let ((*package* (find-package :snowgrave.result-owners.fixture)))
    (dolist (call '("(funcall #'values nil (opaque))"
                    "(apply #'values (list nil (opaque)))"
                    "(multiple-value-call #'values (values nil (opaque)))"
                    "(multiple-value-call #'values (values) (values nil) (values (opaque)))"
                    "(multiple-value-call #'values (values nil) (opaque))"
                    "(multiple-value-call #'values (values) (values nil (opaque)) (values))"))
      (let* ((forms (read-from-string
                     (format nil
                      "((defclass marker () ())
                        (defun entry ()
                          (multiple-value-bind (first second) ~A
                            (declare (ignore first)) (typep second 'marker))))" call)))
             (condition
               (handler-case
                   (progn
                     (snowgrave:close-source-unit
                      (list :forms forms) :unit-name (list 'opaque-secondary-origin call)
                      :closed-classes (list (intern "MARKER")) :universe (read-from-string "(marker t symbol)")
                      :entries (list (intern "ENTRY")) :external-domains (list (list (intern "ENTRY") nil))
                      :external-operations (list (intern "OPAQUE"))) nil)
                 (snowgrave:snowgrave-error (condition) condition))))
        (check (typep condition 'snowgrave:unclosed-call))
        (check (eq :external-result-class-observation (snowgrave:error-feature condition)))))
    ;; A secondary opaque function cannot become a proved closed callback.
    ;; The unclassified external owner includes unknown native return tails.
    (dolist (call '("(multiple-value-call #'values (values nil (opaque)))"
                    "(multiple-value-call #'values (values nil) (opaque))"))
      (let* ((forms (read-from-string
                     (format nil "((defun entry ()
                                    (multiple-value-bind (ignored callback) ~A
                                      (declare (ignore ignored)) (funcall callback))))" call)))
             (condition
               (handler-case
                   (progn
                     (snowgrave:close-source-unit
                      (list :forms forms) :unit-name (list 'opaque-secondary-callback call)
                      :universe '(t function) :entries (list (intern "ENTRY"))
                      :external-domains (list (list (intern "ENTRY") nil))
                      :external-operations (list (intern "OPAQUE"))) nil)
                 (snowgrave:snowgrave-error (condition) condition))))
        (check (typep condition 'snowgrave:unclosed-call))
        (check (member (snowgrave:error-feature condition)
                       '(:computed-function :external-result-escape)))))))
