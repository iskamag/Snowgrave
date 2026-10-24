(in-package #:snowgrave)

;;; Some standard macros expand into host-only helper operations. Adapters
;;; translate those helpers back to ordinary source before the generic passes.
;;; They do not select methods, infer component state, or inspect compiler IR.
(defgeneric normalize-host-operation (operator form))
(defmethod normalize-host-operation (operator form)
  (declare (ignore operator)) form)

(defgeneric normalize-host-declaration (name declaration))
(defmethod normalize-host-declaration (name declaration)
  (declare (ignore name)) declaration)

(defun normalize-host-expression (form)
  (if (consp form) (normalize-host-operation (first form) form) form))
