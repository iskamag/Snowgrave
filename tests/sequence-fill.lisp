(defpackage #:snowgrave.sequence-fill.fixture (:use #:cl))
(in-package #:snowgrave.tests)

(defun sequence-fill-tests ()
  (let* ((*package* (find-package :snowgrave.sequence-fill.fixture))
         (forms (read-from-string
                 "((defclass holder () ((data :initarg :data)))
                   (defun boot () (make-instance 'holder :data (vector 1 2 3 4)))
                   (defun data (owner) (slot-value owner 'data))
                   (defun direct (data)
                     (fill data 9 :start 1 :end 3))
                   (defun indirect (data)
                     (funcall #'fill data 8 :start 1 :end 3))
                   (defun via-apply (data)
                     (apply #'fill data 7 (list :start 1 :end 3)))
                   (defun via-values (data)
                     (multiple-value-call #'fill (values data 6 :start 1 :end 3)))
                   (defun clear-list ()
                     (let ((values (list 1 2 3 4)))
                       (values (fill values nil :start 1 :end 3) values))))"))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(:sequence-fill)
                :closed-classes (read-from-string "(holder)")
                :universe (read-from-string "(holder vector)")
                :entries (read-from-string "(boot data direct indirect via-apply via-values clear-list)")
                :external-domains
                (read-from-string
                 "((boot ()) (data (holder)) (direct (vector)) (indirect (vector))
                   (via-apply (vector)) (via-values (vector)) (clear-list ()))"))))
    (dolist (form forms) (eval form))
    (dolist (name '("DIRECT" "INDIRECT" "VIA-APPLY" "VIA-VALUES"))
      (let* ((native (funcall (intern "BOOT")))
             (closed (funcall (test-unit-function unit "BOOT")))
             (data (funcall (test-unit-function unit "DATA") closed))
             (expected (funcall (intern name) (funcall (intern "DATA") native)))
             (actual (funcall (test-unit-function unit name) data)))
        (check (eq actual data))
        (check (equalp expected actual))))
    (let ((values (multiple-value-list (funcall (test-unit-function unit "CLEAR-LIST")))))
      (check (eq (first values) (second values)))
      (check (equal '(1 nil nil 4) (first values))))
    ;; FILL must not bypass the existing aggregate alias/state audit merely
    ;; because the write is performed through an ordinary sequence function.
    (let ((external (intern "OBSERVE-SHARED")))
      (eval `(defun ,external () nil))
      (dolist (body '("(fill (data owner) owner)"
                      "(funcall #'fill (data owner) owner)"
                      "(apply #'fill (data owner) owner (list :start 1))"
                      "(multiple-value-call #'fill (values (data owner) owner))"))
        (check
         (handler-case
             (progn
               (snowgrave:close-source-unit
                (list :forms (append (subseq forms 0 3)
                                     (list (read-from-string
                                            (format nil "(defun leak (owner) ~A)" body)))))
                :unit-name (list :sequence-fill-shared body)
                :closed-classes (read-from-string "(holder)") :universe (read-from-string "(holder)")
                :entries (read-from-string "(boot leak)")
                :external-domains (read-from-string "((boot ()) (leak (holder)))")
                :external-operations (list external))
               nil)
           (snowgrave:unclosed-call (condition)
             (eq :external-shared-state-representation (snowgrave:error-feature condition)))))))
    (check
     (handler-case
         (progn
           (snowgrave:close-source-unit
            (list :forms (append (subseq forms 0 3)
                                 (list (read-from-string
                                        "(defun clear-unknown (owner) (fill (data owner) nil))"))))
            :unit-name '(:unknown-fill-sequence)
            :closed-classes (read-from-string "(holder)") :universe (read-from-string "(holder)")
            :entries (read-from-string "(boot clear-unknown)")
            :external-domains (read-from-string "((boot ()) (clear-unknown (holder)))"))
           nil)
       (snowgrave:unclosed-call (condition)
         (eq :fill-sequence-domain (snowgrave:error-feature condition)))))
    ;; A returned FILL sequence keeps its source provenance, even when the
    ;; replacement element is independently unclassified. Mutation admission
    ;; is audited separately from this identity-preserving result fact.
    (let* ((build (snowgrave.sbcl::make-build
                   :identity '(:fill-result-origin)
                   :source (snowgrave:make-authored-source nil)))
           (snowgrave.sbcl::*argument-domains* '((source . :external-result) (item . :unknown))))
      (check (eq :external-result (snowgrave.sbcl::value-domain build '(fill source nil)))))
    t))
