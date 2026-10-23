(in-package #:snowgrave)

(defun observation-function-name (build name phase)
  (when (eq name 'equalp)
    (if (and (eq phase :closed) (build-classes build))
        (closed-name build '%logical-equalp)
        name)))

(defun emit-observations (build)
  "Preserve CLOS identity when observing closed records inside native data."
  (unless (build-classes build) (return-from emit-observations nil))
  (let ((name (closed-name build '%logical-equalp))
        (left (gensym "LEFT")) (right (gensym "RIGHT")))
    (labels ((recordp (value)
               `(or ,@(loop for description in (build-layouts build)
                            collect `(,(class-description-predicate description) ,value))
                    ,(closed-metadata-object-test build value))))
      (emit-form
       build
       `(defun ,name (,left ,right)
          (cond
            ((eq ,left ,right) t)
            ;; Source standard objects use identity even inside an aggregate.
            ((or ,(recordp left) ,(recordp right)) nil)
            ((and (consp ,left) (consp ,right))
             (and (,name (car ,left) (car ,right))
                  (,name (cdr ,left) (cdr ,right))))
            ((and (arrayp ,left) (arrayp ,right))
             (if (and (vectorp ,left) (vectorp ,right))
                 (and (= (length ,left) (length ,right))
                      (loop for index below (length ,left)
                            always (,name (aref ,left index) (aref ,right index))))
                 (and (equal (array-dimensions ,left) (array-dimensions ,right))
                      (loop for index below (array-total-size ,left)
                            always (,name (row-major-aref ,left index)
                                          (row-major-aref ,right index))))))
            ;; Opaque native containers could conceal closed records. Their
            ;; storage/key protocols need an explicit realization before use.
            ((or (typep ,left 'structure-object) (typep ,right 'structure-object)
                 (hash-table-p ,left) (hash-table-p ,right))
             (error "EQUALP on opaque native containers is outside the closed observation domain."))
            (t (equalp ,left ,right))))))))
