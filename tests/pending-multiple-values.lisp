(defpackage #:snowgrave.pending-mvb.fixture (:use #:cl))
(in-package #:snowgrave.tests)

(cl:defclass snowgrave.pending-mvb.fixture::marker () ())
(defvar snowgrave.pending-mvb.fixture::*events* nil)
(defun snowgrave.pending-mvb.fixture::observe (tag)
  (push tag snowgrave.pending-mvb.fixture::*events*) nil)
(defun snowgrave.pending-mvb.fixture::opaque ()
  (make-instance 'snowgrave.pending-mvb.fixture::marker))
(defun snowgrave.pending-mvb.fixture::opaque-values ()
  (values nil (snowgrave.pending-mvb.fixture::opaque)))
(defvar *pending-mvb-unit-sequence* 0)

(defun pending-mvb-forms (definitions entry)
  (let ((*package* (find-package :snowgrave.pending-mvb.fixture)))
    (read-from-string (format nil "((defclass marker () ()) ~A ~A)" definitions entry))))
(defun eval-pending-mvb-forms (forms)
  (when (fboundp 'snowgrave.pending-mvb.fixture::produce)
    (fmakunbound 'snowgrave.pending-mvb.fixture::produce))
  (dolist (form forms) (eval form)))
(defun close-pending-mvb (forms name domains &key genericp)
  (let ((*package* (find-package :snowgrave.pending-mvb.fixture)))
    (snowgrave:close-source-unit
     (list :forms forms) :unit-name (list 'pending-multiple-values name (incf *pending-mvb-unit-sequence*))
     :closed-classes (list (intern "MARKER")) :closed-generics (when genericp (list (intern "PRODUCE")))
     :universe (read-from-string "(marker integer number vector symbol t)")
     :entries (list (intern "ENTRY")) :external-domains (list (list (intern "ENTRY") domains))
     :external-operations (mapcar #'intern '("OBSERVE" "OPAQUE" "OPAQUE-VALUES")))))
(defun pending-mvb-outcome (thunk)
  (handler-case (cons :values (multiple-value-list (funcall thunk)))
    (type-error (condition)
      (list :type-error (type-error-datum condition) (type-error-expected-type condition)))))
(defun check-pending-mvb-refusal (forms name domains feature)
  (let ((condition (handler-case (progn (close-pending-mvb forms name domains) nil)
                     (snowgrave:snowgrave-error (condition) condition))))
    (check (typep condition 'snowgrave:unclosed-call))
    (check (eq feature (snowgrave:error-feature condition)))))

(defun pending-multiple-value-tests ()
  (let ((*package* (find-package :snowgrave.pending-mvb.fixture)))
    ;; The relay must not acquire an irreversible UNKNOWN result merely
    ;; because its ordinary or generic producer is still pending this pass.
    (dolist (kind '(:direct :producer-first :caller-first :generic))
      (let* ((producer "(defun produce (x) (values (logand x -8) t))")
             (relay (if (eq kind :direct) "(defun relay (x) (produce x))"
                        "(defun relay (x) (multiple-value-bind (start present) (produce x)
                                             (when present (values start t))))"))
             (definitions (case kind
                            (:caller-first (format nil "~A ~A" relay producer))
                            (:generic (format nil "(defgeneric produce (x))
                                                   (defmethod produce (x) (values (logand x -8) t)) ~A" relay))
                            (t (format nil "~A ~A" producer relay))))
             (forms (pending-mvb-forms definitions
                       "(defun entry (target x) (setf (svref target 0) (relay x)))")))
        (eval-pending-mvb-forms forms)
        (let* ((native-target (vector nil)) (closed-target (vector nil))
               (unit (close-pending-mvb forms kind '(vector integer) :genericp (eq kind :generic))))
          (check (= 16 (funcall (intern "ENTRY") native-target 19)))
          (check (= 16 (funcall (snowgrave:unit-function unit (intern "ENTRY")) closed-target 19)))
          (check (equalp native-target closed-target)))))
    ;; Complete zero/short tuples still receive ordinary NIL padding.
    (dolist (spec '((:zero "(values)" (nil nil nil))
                    (:short "(values 17 :tag)" (17 :tag nil))))
      (let* ((forms (pending-mvb-forms (format nil "(defun produce () ~A)" (second spec))
                       "(defun entry () (multiple-value-bind (a b c) (produce) (values a b c)))"))
             (unit (close-pending-mvb forms (first spec) nil)))
        (eval-pending-mvb-forms forms)
        (check (equal (third spec) (multiple-value-list (funcall (intern "ENTRY")))))
        (check (equal (third spec) (multiple-value-list (funcall (snowgrave:unit-function unit (intern "ENTRY"))))))))
    ;; The MVB relay preserves producer-before-cleanup effects and the native
    ;; arithmetic condition on the failing branch, as well as normal values.
    (let* ((forms (pending-mvb-forms
                    "(defun produce (failp) (observe :producer)
                       (values (logand (if failp :bad 19) -8) t))
                     (defun relay (failp)
                       (multiple-value-bind (start present)
                           (unwind-protect (produce failp) (observe :cleanup))
                         (when present (values start t))))"
                    "(defun entry (failp) (relay failp))"))
           (unit (close-pending-mvb forms :effects-and-conditions '(symbol))))
      (eval-pending-mvb-forms forms)
      (dolist (flag '(nil t))
        (setf snowgrave.pending-mvb.fixture::*events* nil)
        (let ((native (pending-mvb-outcome (lambda () (funcall (intern "ENTRY") flag))))
              (events nil))
          (setf events (reverse snowgrave.pending-mvb.fixture::*events*)
                snowgrave.pending-mvb.fixture::*events* nil)
          (check (eq (if flag :type-error :values) (car native)))
          (check (equal native
                        (pending-mvb-outcome (lambda () (funcall (snowgrave:unit-function unit (intern "ENTRY")) flag)))))
          (check (equal '(:producer :cleanup) events))
          (check (equal events (reverse snowgrave.pending-mvb.fixture::*events*))))))
    ;; Pending must later become the actual opaque position/tail contract,
    ;; never a native UNKNOWN fact that authorizes logical class observation.
    (dolist (producer '("(values nil (opaque))" "(opaque-values)"))
      (let ((forms (pending-mvb-forms (format nil "(defun produce () ~A)" producer)
                     "(defun entry () (multiple-value-bind (first second) (produce)
                                        (declare (ignore first)) (typep second 'marker)))")))
        (eval-pending-mvb-forms forms)
        (check (funcall (intern "ENTRY")))
        (check-pending-mvb-refusal forms (list :opaque-tail producer) nil :external-result-class-observation)))
    ;; A genuine incomplete count does not prove NIL beyond its prefix.
    (let ((forms (pending-mvb-forms
                   "(defun produce (flag) (if flag (values 17) (values 17 :tag)))"
                   "(defun entry (target flag) (multiple-value-bind (a b c) (produce flag)
                                                (declare (ignore a b)) (setf (svref target 0) c)))")))
      (eval-pending-mvb-forms forms)
      (check (null (funcall (intern "ENTRY") (vector :old) t)))
      (check-pending-mvb-refusal forms :incomplete-tail '(vector symbol) :external-shared-state-representation))
    ;; A no-base recursion has no finite normal tuple. Closure must reach its
    ;; existing quiescent UNKNOWN settlement and refuse the unproved store;
    ;; the test deliberately does not execute the nonterminating function.
    (let ((forms (pending-mvb-forms "(defun produce () (produce))"
                   "(defun entry (target) (multiple-value-bind (a b) (produce)
                                           (declare (ignore b)) (setf (svref target 0) a)))")))
      (check-pending-mvb-refusal forms :recursive-no-base '(vector) :external-shared-state-representation))))
