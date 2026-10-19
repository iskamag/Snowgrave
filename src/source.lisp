(in-package #:snowgrave)

(defvar *definition-recorder* nil)

(defun array-allocation-options (array displaced-to)
  "Describe the observable native array geometry, without its element data."
  (multiple-value-bind (parent offset) (array-displacement array)
    (append (list :element-type (array-element-type array)
                  :adjustable (not (null (adjustable-array-p array))))
            (when (array-has-fill-pointer-p array) (list :fill-pointer (fill-pointer array)))
            (when parent (list :displaced-to displaced-to :displaced-index-offset offset)))))

(defun acyclic-array-displacement-p (array checked)
  "Check allocation dependencies only; array element edges may be cyclic."
  (let ((path nil) (seen (make-hash-table :test #'eq)))
    (loop for current = array then (array-displacement current) while current do
      (when (gethash current checked) (return))
      (when (gethash current seen) (return-from acyclic-array-displacement-p nil))
      (setf (gethash current seen) t)
      (push current path))
    (dolist (node path) (setf (gethash node checked) t))
    t))

(defun immutable-copy (value &optional copy-observer)
  "Own mutable cons/array data, preserving sharing, cycles and array geometry."
  (let ((copies (make-hash-table :test #'eq)) (displacements (make-hash-table :test #'eq)))
    (labels ((copy-array (array)
               (or (gethash array copies)
                   (progn
                     (unless (acyclic-array-displacement-p array displacements)
                       (reject 'nonreproducible-source :source-admission :array-displacement-cycle
                               "An array displacement chain must have an allocated base."))
                     (let* ((parent (array-displacement array))
                            (backing (when parent (copy parent))))
                       ;; Parent data can lead back to this view. That path
                       ;; may already have allocated it against the new base.
                       (or (gethash array copies)
                           (let ((result (apply #'make-array (array-dimensions array)
                                                (array-allocation-options array backing))))
                             (setf (gethash array copies) result)
                             (unless (or parent (null (array-element-type array)))
                               (dotimes (index (array-total-size array))
                                 (setf (row-major-aref result index)
                                       (copy (row-major-aref array index)))))
                             result))))))
             (copy (x)
               (cond ((consp x)
                      (or (gethash x copies)
                          (let ((result (cons nil nil)))
                            (setf (gethash x copies) result
                                  (car result) (copy (car x))
                                  (cdr result) (copy (cdr x))) result)))
                     ((arrayp x) (copy-array x))
                     (t x))))
      (let ((result (copy value)))
        (when copy-observer (maphash copy-observer copies))
        result))))

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
