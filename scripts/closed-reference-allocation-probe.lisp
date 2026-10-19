;;;; Successful closed-reference writes, not native supervisor admission.
(require :asdf)
(let* ((root (uiop:pathname-parent-directory-pathname
              (uiop:pathname-directory-pathname *load-truename*)))
       (cache (merge-pathnames ".build/reference-allocation-fasl/" root)))
  (asdf:initialize-source-registry
   `(:source-registry (:directory ,root) :ignore-inherited-configuration))
  (asdf:initialize-output-translations
   `(:output-translations (t ,cache) :ignore-inherited-configuration)))
(asdf:load-system "snowgrave/sbcl")

(defpackage #:snowgrave.reference-allocation.fixture (:use #:cl))
(in-package #:cl-user)

(defvar *reference-allocation-calibration* nil)

(defun reference-allocation-control ()
  (let ((values nil))
    (dotimes (index 10000) (push index values))
    (setf *reference-allocation-calibration* values)))

(defun reference-allocation-sample (function &rest arguments)
  ;; This measurement wrapper's argument list is created before sampling.
  (let* ((before (sb-ext:get-bytes-consed))
         (result (apply function arguments))
         (bytes (- (sb-ext:get-bytes-consed) before)))
    (values bytes result)))

(let* ((*package* (find-package :snowgrave.reference-allocation.fixture))
       (forms
         (read-from-string
          "((defclass node () ((next :type node :accessor next)))
            (defclass holder () ((child :type node :initarg :child :accessor child)))
            (defun boot ()
              (let ((value (make-instance 'node)))
                (setf (next value) value)
                (make-instance 'holder :child value)))
            (defun child-of (owner) (child owner))
            (defun assign (owner value) (setf (child owner) value))
            (defun repeat-write (owner value)
              (dotimes (index 10000) (setf (child owner) value))
              :written))"))
       (unit
         (snowgrave:close-source-unit
          (list :forms forms) :unit-name '(:closed-reference-allocation :version 1)
          :closed-classes (read-from-string "(node holder)")
          :closed-generics (read-from-string "(next (setf next) child (setf child))")
          :universe (read-from-string "(node holder)")
          :entries (read-from-string "(boot child-of assign repeat-write)")
          :external-domains
          (read-from-string "((boot ()) (child-of (holder)) (assign (holder node))
                              (repeat-write (holder node)))")))
       (boot (snowgrave:unit-function unit (intern "BOOT")))
       (reader (snowgrave:unit-function unit (intern "CHILD-OF")))
       (assign (snowgrave:unit-function unit (intern "ASSIGN")))
       (repeat-write (snowgrave:unit-function unit (intern "REPEAT-WRITE")))
       (owner (funcall boot))
       (value (funcall reader owner)))
  (sb-ext:gc :full t)
  (let ((control (reference-allocation-sample #'reference-allocation-control)))
    (unless (plusp control) (error "Allocation calibration did not detect allocation"))
    (multiple-value-bind (first-bytes result)
        (reference-allocation-sample assign owner value)
      (assert (eq result value))
      (funcall repeat-write owner value)
      (multiple-value-bind (warm-bytes result)
          (reference-allocation-sample repeat-write owner value)
        (assert (eq result :written))
        (assert (eq value (funcall reader owner)))
        (format t "CLOSED REFERENCE WRITES: first assign entry=~D bytes; 10000 warmed writes=~D bytes; allocation control=~D bytes.~%"
                first-bytes warm-bytes control)
        (unless (and (zerop first-bytes) (zerop warm-bytes))
          (error "Successful closed-reference writes allocated")))))
  (format t "HOSTED allocation observation only; native layout, residency and failure entries are separate obligations.~%"))
