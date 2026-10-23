(eval-when (:compile-toplevel :load-toplevel :execute) (require :sb-cltl2))

(defpackage #:snowgrave
  (:use #:common-lisp)
  (:export #:close-source-unit #:closed-unit #:closed-unit-p
           #:unit-function #:unit-source #:unit-metadata #:unit-report
           #:write-unit-source #:write-unit-metadata
           #:snowgrave-error #:unsupported-definition #:unclosed-call
           #:error-feature #:error-detail))

(in-package #:snowgrave)

(define-condition snowgrave-error (error)
  ((feature :initarg :feature :reader error-feature)
   (detail :initarg :detail :reader error-detail))
  (:report (lambda (condition stream)
             (format stream "Snowgrave ~S: ~A" (error-feature condition) (error-detail condition)))))
(define-condition unsupported-definition (snowgrave-error) ())
(define-condition unclosed-call (snowgrave-error) ())

(defun unsupported (build feature control &rest arguments)
  (declare (ignore build))
  (error 'unsupported-definition :feature feature :detail (apply #'format nil control arguments)))

(defstruct build
  identity declaration forms open-package output-package
  classes functions generics globals method-sources layouts
  (generated nil) (sequence 0)
  (open-names (make-hash-table :test #'equal))
  (closed-names (make-hash-table :test #'equal))
  (open-literals (make-array 0 :adjustable t :fill-pointer 0))
  (closed-literals (make-array 0 :adjustable t :fill-pointer 0))
  (open-literal-index (make-hash-table :test #'eq))
  (closed-literal-index (make-hash-table :test #'eq))
  open-literal-name closed-literal-name
  (temporary-methods nil))

(defun mapped-name (build name phase)
  (if (consp name)
      (list 'setf (mapped-name build (second name) phase))
      (let ((table (if (eq phase :open) (build-open-names build) (build-closed-names build)))
            (package (if (eq phase :open) (build-open-package build) (build-output-package build))))
        (or (gethash name table)
            (setf (gethash name table)
                  (intern (format nil "~A-~D" (symbol-name name) (hash-table-count table)) package))))))
(defun open-name (build name) (mapped-name build name :open))
(defun closed-name (build name) (mapped-name build name :closed))
(defun fresh-name (build prefix)
  (intern (format nil "%~A-~D" prefix (incf (build-sequence build))) (build-output-package build)))
(defun emit-form (build form) (push form (build-generated build)) form)

(defun function-name-p (name)
  (or (symbolp name) (and (consp name) (eq (first name) 'setf)
                         (consp (rest name)) (null (cddr name)) (symbolp (second name)))))
(defun source-function-p (build name)
  (member name (append (build-functions build) (build-generics build)) :test #'equal))
(defun source-class-p (build name) (member name (build-classes build)))
(defun quoted (form)
  (and (consp form) (eq (first form) 'quote) (consp (rest form)) (null (cddr form))))
