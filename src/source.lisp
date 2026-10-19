(in-package #:snowgrave)

(defvar *definition-recorder* nil)

(defun immutable-copy (value)
  "Own mutable cons/string/simple-vector data, preserving graph sharing."
  (let ((copies (make-hash-table :test #'eq)))
    (labels ((copy (x)
               (cond ((consp x)
                      (or (gethash x copies)
                          (let ((result (cons nil nil)))
                            (setf (gethash x copies) result
                                  (car result) (copy (car x))
                                  (cdr result) (copy (cdr x))) result)))
                     ((stringp x) (or (gethash x copies)
                                      (setf (gethash x copies) (copy-seq x))))
                     ((simple-vector-p x)
                      (or (gethash x copies)
                          (let ((result (make-array (length x))))
                            (setf (gethash x copies) result)
                            (dotimes (index (length x))
                              (setf (svref result index) (copy (svref x index))))
                            result)))
                     (t x))))
      (copy value))))

(defun record-authored-definition (kind name form)
  (when *definition-recorder*
    (funcall *definition-recorder* kind name form))
  nil)

(defmacro defclass (&whole form name superclasses slots &rest options)
  `(progn
     (eval-when (:compile-toplevel :load-toplevel :execute)
       (record-authored-definition :class ',name ',form))
     (cl:defclass ,name ,superclasses ,slots ,@options)))

(defmacro defgeneric (&whole form name lambda-list &rest options)
  `(progn
     (eval-when (:compile-toplevel :load-toplevel :execute)
       (record-authored-definition :generic ',name ',form))
     (cl:defgeneric ,name ,lambda-list ,@options)))

(defmacro defmethod (&whole form name &rest tail)
  `(progn
     (eval-when (:compile-toplevel :load-toplevel :execute)
       (record-authored-definition :method ',name ',form))
     (cl:defmethod ,name ,@tail)))

(defmacro define-method-combination (&whole form name &rest definition)
  `(progn
     (eval-when (:compile-toplevel :load-toplevel :execute)
       (record-authored-definition :method-combination ',name ',form))
     (cl:define-method-combination ,name ,@definition)))
