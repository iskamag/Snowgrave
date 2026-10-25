(in-package #:snowgrave)

;;; Literal pools preserve sharing and cycles without embedding live objects.

(defun copy-source-graph (object)
  "Own the source without changing identity relationships between literals."
  (let ((copies (make-hash-table :test #'eq)))
    (labels ((copy (value)
               (cond ((consp value)
                      (or (gethash value copies)
                          (let ((cell (cons nil nil)))
                            (setf (gethash value copies) cell
                                  (car cell) (copy (car value)) (cdr cell) (copy (cdr value)))
                            cell)))
                     ((stringp value)
                      (or (gethash value copies) (setf (gethash value copies) (copy-seq value))))
                     ((simple-vector-p value)
                      (or (gethash value copies)
                          (let ((vector (make-array (length value))))
                            (setf (gethash value copies) vector)
                            (dotimes (i (length value)) (setf (aref vector i) (copy (aref value i))))
                            vector)))
                     (t value))))
      (copy object))))

(defun literal-reference (build object phase)
  (let ((index (if (eq phase :open) (build-open-literal-index build) (build-closed-literal-index build)))
        (values (if (eq phase :open) (build-open-literals build) (build-closed-literals build)))
        (name (if (eq phase :open) (build-open-literal-name build) (build-closed-literal-name build))))
    (labels ((enter (value)
               (cond ((or (consp value) (stringp value) (simple-vector-p value))
                      (multiple-value-bind (position present) (gethash value index)
                        (unless present
                          (setf position (vector-push-extend value values)
                                (gethash value index) position)
                          (cond ((consp value) (enter (car value)) (enter (cdr value)))
                                ((simple-vector-p value) (map nil #'enter value))))
                        `(aref ,name ,position)))
                     ((or (null value) (symbolp value) (numberp value) (characterp value)) `',value)
                     (t (unsupported :literal "Unsupported literal representation ~S." (type-of value))))))
      (enter object))))

(defun literal-definition (build phase)
  (let* ((objects (if (eq phase :open) (build-open-literals build) (build-closed-literals build)))
         (name (if (eq phase :open) (build-open-literal-name build) (build-closed-literal-name build)))
         (index (if (eq phase :open) (build-open-literal-index build) (build-closed-literal-index build)))
         (nodes (gensym "LITERALS")) (recipes (gensym "RECIPES"))
         (recipe (gensym "RECIPE")) (position (gensym "POSITION"))
         (value (gensym "VALUE")) (decode (gensym "DECODE")) (element (gensym "ELEMENT")))
    (when (plusp (length objects))
      (if (every #'stringp objects)
          ;; Identity among strings is preserved by the caller's own copies, so
          ;; no recipe interpreter is needed: allocate each string once.
          `(defparameter ,name
             (vector ,@(map 'list (lambda (value) `(copy-seq ,value)) objects)))
          (labels ((reference (value)
                     (multiple-value-bind (i present) (gethash value index)
                       ;; Every compound literal is a pool node. A one-element
                       ;; list in this immutable recipe is therefore an index;
                       ;; scalar literals (including integer indices) stay scalar.
                       (if present (list i) value))))
            `(defparameter ,name
              (let* ((,recipes
                       ',(map 'vector
                              (lambda (value)
                                (cond ((consp value)
                                       (vector :cons (reference (car value)) (reference (cdr value))))
                                      ((stringp value) (vector :string value))
                                      (t (vector :vector (map 'vector #'reference value)))))
                              objects))
                     (,nodes (make-array (length ,recipes))))
               ;; Allocate every node before installing any edge. The compiled
               ;; initializer is constant-size; graph size belongs to data.
                (dotimes (,position (length ,recipes))
                  (let ((,recipe (aref ,recipes ,position)))
                    (setf (aref ,nodes ,position)
                          (ecase (aref ,recipe 0)
                            (:cons (cons nil nil))
                            (:string (copy-seq (aref ,recipe 1)))
                            (:vector (make-array (length (aref ,recipe 1))))))))
                (flet ((,decode (,value)
                         (if (consp ,value) (aref ,nodes (car ,value)) ,value)))
                  (dotimes (,position (length ,recipes))
                    (let ((,recipe (aref ,recipes ,position)))
                      (case (aref ,recipe 0)
                        (:cons
                         (setf (car (aref ,nodes ,position)) (,decode (aref ,recipe 1))
                               (cdr (aref ,nodes ,position)) (,decode (aref ,recipe 2))))
                        (:vector
                         (dotimes (,element (length (aref ,recipe 1)))
                           (setf (aref (aref ,nodes ,position) ,element)
                                 (,decode (aref (aref ,recipe 1) ,element)))))))))
              ,nodes)))))))
