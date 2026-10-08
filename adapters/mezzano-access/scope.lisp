;;;; Mezzano target-only cold lowering. This system has no pager or builder owner.
(defpackage #:snowgrave.mezzano-access
  (:use #:cl)
  (:export #:with-admitted-access #:admitted-access-failure #:access-call-arguments
           #:define-record-accessors #:define-record-predicate
           #:define-admitted-entry #:admitted-lambda #:call-admitted-entry))
(in-package #:snowgrave.mezzano-access)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun access-call-arguments (form name)
    "Return finite arguments and a flag for exact direct/literal FUNCALL syntax.
This cold syntax operation does not itself authorize raw lowering or arity."
    (when (consp form)
      (let ((arguments
              (cond ((equal (car form) name) (cdr form))
                    ((and (eq (car form) 'funcall) (consp (second form))
                          (member (car (second form)) '(function quote))
                          (equal (second (second form)) name) (null (cddr (second form))))
                     (cddr form))
                    (t (return-from access-call-arguments (values nil nil))))))
        (when (handler-case (not (null (list-length arguments))) (type-error () nil))
          (values arguments t)))))

  (defun admitted-access-failure (environment)
    "Return the exact caller's lexical bounded failure form and an admission flag.
A global macro with the marker name does not grant access. The caller owns
code/layout/data residence, lifetime, mutation exclusion and the failure action."
    (when environment
      (let ((marker (macro-function '%admitted-access-scope environment)))
        (when (and marker (not (eq marker (macro-function '%admitted-access-scope))))
          (values (funcall marker '(%admitted-access-scope) environment) t)))))

  (defmacro with-admitted-access (failure-form &body body)
    "Lower supported native access calls inside BODY, or execute FAILURE-FORM.
For example: (WITH-ADMITTED-ACCESS (RETURN-FROM ENTRY (VALUES NIL :INVALID))
               (RECORD-VALUE RECORD)). The form's block names remain lexical.
This scope does not itself admit residence, transitive code or callable values."
    `(macrolet ((%admitted-access-scope () ',failure-form)) ,@body)))
