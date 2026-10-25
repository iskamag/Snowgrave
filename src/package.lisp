(defpackage #:snowgrave
  (:use #:common-lisp)
  (:export #:close-source-unit #:closed-unit #:closed-unit-p
           #:unit-function #:unit-source #:unit-metadata #:unit-report
           #:write-unit-source #:write-unit-metadata
           #:bind-entry
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

(defun unsupported (feature control &rest arguments)
  (error 'unsupported-definition :feature feature :detail (apply #'format nil control arguments)))
