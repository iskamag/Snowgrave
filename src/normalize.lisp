(in-package #:snowgrave)

;; Snapshot host macroexpansion before either namespace is constructed.
;; Both compilations then consume the same expanded source and literal graph.
(defun normalize-source-expression (form environment)
  (walk-source-form
   form environment
   (lambda (node context lexical)
     (declare (ignore lexical))
     (if (and (eq context :eval) (consp node) (eq (first node) 'quote))
         ;; Literal identity is independent of the shape of its source use.
         (values node t)
         node))))

(defun normalize-source-lambda (name lambda-list body environment)
  (multiple-value-bind (prefix executable) (body-parts body)
    (normalize-source-expression
     `(lambda ,lambda-list ,@prefix ,(source-block-form name executable))
     environment)))

(defun normalize-source-class (form environment)
  (map-class-definition
   form #'identity
   (lambda (key value)
     (if (eq key :initform) (normalize-source-expression value environment) value))))

(defun normalize-source-method (form environment)
  (multiple-value-bind (qualifiers lambda-list body) (method-parts form)
    (let* ((name (second form))
           (ordinary (ordinary-method-lambda-list lambda-list))
           (required (position-if (lambda (item) (member item lambda-list-keywords)) lambda-list))
           (count (or required (length lambda-list)))
           (normalized (normalize-source-lambda name ordinary body environment)))
      ;; The lexical walker sees ordinary variable bindings. Restore only the
      ;; required specializers; optional/key initforms come from its snapshot.
      `(defmethod ,name ,@qualifiers
           ,(append (subseq lambda-list 0 count) (nthcdr count (second normalized)))
         ,@(cddr normalized)))))

(defun normalize-owned-source (build)
  "Freeze owned bodies and initializers once, preserving names and literals."
  (let ((environment
          (cl-environments:augment-environment
           nil :function (remove-duplicates (append (build-functions build) (build-generics build))
                                            :test #'equal))))
    (setf (build-forms build)
          (mapcar
           (lambda (form)
             (case (first form)
               (defun
                (let ((normalized (normalize-source-lambda (second form) (third form)
                                                          (cdddr form) environment)))
                  (list* 'defun (second form) (rest normalized))))
               (defmethod (normalize-source-method form environment))
               (defclass (normalize-source-class form environment))
               ((defvar defparameter defconstant)
                (if (cddr form)
                    (list* (first form) (second form)
                           (normalize-source-expression (third form) environment)
                           (cdddr form))
                    form))
               (otherwise form)))
           (build-forms build)))
    (setf (build-method-sources build)
          (remove-if-not (lambda (form) (eq (first form) 'defmethod)) (build-forms build))))
  build)
