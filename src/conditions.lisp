(in-package #:snowgrave)

(define-condition snowgrave-error (error)
  ((source-key :initarg :source-key :initform nil :reader error-source-key)
   (feature :initarg :feature :reader error-feature)
   (phase :initarg :phase :reader error-phase)
   (path :initarg :path :initform nil :reader error-path)
   (detail :initarg :detail :reader error-detail))
  (:report (lambda (condition stream)
             (format stream "Snowgrave ~A: ~A~@[ at ~S~] (~A)~@[; path ~S~]"
                     (error-phase condition) (error-feature condition)
                     (error-source-key condition) (error-detail condition)
                     (error-path condition)))))

(define-condition unsupported-definition (snowgrave-error) ())
(define-condition unclosed-call (snowgrave-error) ())
(define-condition unclosed-class-operation (snowgrave-error) ())
(define-condition nonreproducible-source (snowgrave-error) ())
(define-condition mop-failure (snowgrave-error) ())
(define-condition incomplete-domain (snowgrave-error) ())
(define-condition residual-metaobject (snowgrave-error) ())
(define-condition audit-failure (snowgrave-error) ())

(defun reject (type phase feature detail &key source-key path)
  (error type :phase phase :feature feature :detail detail
              :source-key source-key :path path))

(define-condition domain-violation (error)
  ((unit :initarg :unit :reader violation-unit)
   (name :initarg :name :reader violation-name)
   (arguments :initarg :arguments :reader violation-arguments))
  (:report (lambda (condition stream)
             (format stream "Argument tuple outside Snowgrave unit ~S entry ~S: ~S"
                     (violation-unit condition) (violation-name condition)
                     (violation-arguments condition)))))

(defun sg-domain-violation (unit name arguments)
  "The portable non-returning action; never performs CLOS method selection."
  (error 'domain-violation :unit unit :name name :arguments arguments))
