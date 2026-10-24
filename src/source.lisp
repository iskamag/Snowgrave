(in-package #:snowgrave)

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

(defun read-source (source)
  (unless (and (listp source) (member (first source) '(:forms :files)))
    (unsupported nil :source-unit "Expected (:FORMS forms) or (:FILES pathnames...)."))
  (copy-source-graph
   (ecase (first source)
     (:forms (second source))
     (:files
      (let ((*package* *package*) (*read-eval* nil) (forms nil))
        (dolist (path (rest source))
          (with-open-file (stream path)
            (loop for form = (read stream nil stream) until (eq form stream)
                  do (case (and (consp form) (first form))
                       (in-package (setf *package* (or (find-package (second form))
                                                     (unsupported nil :source-package "Unknown package ~S." (second form)))))
                       (defpackage (unsupported nil :source-package "Create source packages before closing."))
                       (otherwise (push form forms))))))
        (nreverse forms))))))

(defun method-parts (form)
  (let ((tail (cddr form)) (qualifiers nil))
    (loop while (and tail (not (listp (first tail)))) do (push (pop tail) qualifiers))
    (values (nreverse qualifiers) (first tail) (rest tail))))

(defun index-source (build)
  (let ((forms (build-forms build)))
    (unless (and forms (ignore-errors (list-length forms)))
      (unsupported build :source-sequence "Source must be a finite nonempty ordered list."))
    (dolist (form forms)
      (unless (and (consp form) (function-name-p (second form)))
        (unsupported build :definition "Invalid definition ~S." form))
      (case (first form)
        (defclass
         (push (second form) (build-classes build))
         (dolist (slot (fourth form))
           (when (consp slot)
             (loop for (key value) on (rest slot) by #'cddr
                   do (case key
                        (:reader (pushnew value (build-generics build) :test #'equal))
                        (:writer (pushnew value (build-generics build) :test #'equal))
                        (:accessor (pushnew value (build-generics build) :test #'equal)
                                   (pushnew (list 'setf value) (build-generics build) :test #'equal)))))))
        (defgeneric (pushnew (second form) (build-generics build) :test #'equal))
        (defmethod (push form (build-method-sources build))
                   (pushnew (second form) (build-generics build) :test #'equal))
        (defun (push (second form) (build-functions build)))
        ((defvar defparameter defconstant)
         (push (second form) (build-globals build))
         (when (eq (first form) 'defconstant) (push (second form) (build-constants build))))
        (otherwise (unsupported build :definition "Unsupported top-level form ~S." (first form)))))
    (setf (build-classes build) (nreverse (build-classes build))
          (build-functions build) (nreverse (build-functions build))
          (build-generics build) (nreverse (build-generics build))
          (build-method-sources build) (nreverse (build-method-sources build)))
    (dolist (names (list (build-classes build) (build-functions build) (build-globals build)))
      (unless (= (length names) (length (remove-duplicates names :test #'equal)))
        (unsupported build :redefinition "Repeated source definitions require a new unit.")))
    (dolist (name (append (build-classes build) (build-functions build) (build-generics build)))
      (when (and (symbolp name) (eq (symbol-package name) (find-package :cl))
                 (not (member name '(initialize-instance shared-initialize))))
        (unsupported build :standard-definition "Cannot replace standard definition ~S." name))
      (open-name build name)
      (closed-name build name))))

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
                     (t (unsupported build :literal "Unsupported literal representation ~S." (type-of value))))))
      (enter object))))

(defun literal-definition (build phase)
  (let* ((objects (if (eq phase :open) (build-open-literals build) (build-closed-literals build)))
         (name (if (eq phase :open) (build-open-literal-name build) (build-closed-literal-name build)))
         (index (if (eq phase :open) (build-open-literal-index build) (build-closed-literal-index build)))
         (nodes (gensym "LITERALS")) (recipes (gensym "RECIPES"))
         (recipe (gensym "RECIPE")) (position (gensym "POSITION"))
         (value (gensym "VALUE")) (decode (gensym "DECODE")) (element (gensym "ELEMENT")))
    (when (plusp (length objects))
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
              ,nodes))))))

(defun open-definition (build form)
  (case (first form)
    (defclass
     (destructuring-bind (operator name supers slots &rest options) form
       (declare (ignore operator))
       `(defclass ,(open-name build name)
            ,(mapcar (lambda (super) (if (source-class-p build super) (open-name build super) super)) supers)
          ,(mapcar
            (lambda (slot)
              (if (symbolp slot) slot
                  (cons (first slot)
                        (loop for (key value) on (rest slot) by #'cddr
                              append (list key (case key
                                                 ((:reader :writer :accessor) (open-name build value))
                                                 (:initform (rewrite-form build value :open))
                                                 (:type (rewrite-type build value :open))
                                                 (otherwise value))))))) slots)
          ,@(mapcar (lambda (option)
                      (if (eq (first option) :default-initargs)
                          (cons :default-initargs
                                (loop for (key value) on (rest option) by #'cddr
                                      append (list key (rewrite-form build value :open))))
                          option)) options))))
    (defgeneric
     (list* 'defgeneric (open-name build (second form)) (cddr form)))
    (defmethod
     (multiple-value-bind (qualifiers lambda-list body) (method-parts form)
       (let ((name (second form)))
         (multiple-value-bind (prefix executable) (body-parts body)
           `(defmethod ,(if (member name '(initialize-instance shared-initialize)) name (open-name build name))
                ,@qualifiers
                ,(mapcar (lambda (item)
                           (if (and (consp item) (source-class-p build (second item)))
                               (list (first item) (open-name build (second item))) item)) lambda-list)
              ,@(cddr (rewrite-form build `(lambda ,(ordinary-method-lambda-list lambda-list)
                                             ,@prefix
                                             (block ,(if (consp name) (second name) name) ,@executable))
                                    :open)))))))
    (defun
     (let ((lambda-form (rewrite-form build (cons 'lambda (cddr form)) :open)))
       (list* 'defun (open-name build (second form)) (rest lambda-form))))
    ((defvar defparameter defconstant)
     (list* (first form) (open-name build (second form))
            (when (cddr form) (cons (rewrite-form build (third form) :open) (cdddr form)))))))
