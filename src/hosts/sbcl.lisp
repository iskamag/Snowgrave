(in-package #:snowgrave)

(defmethod normalize-host-declaration ((name (eql 'sb-c::no-debug)) declaration)
  (declare (ignore name declaration)) nil)

(defmethod normalize-host-operation ((operator (eql 'sb-kernel:unaligned-dx-cons)) form)
  (declare (ignore operator))
  ;; LOOP's temporary collection head. Its surrounding DYNAMIC-EXTENT
  ;; declaration still expresses the lifetime of this ordinary cons.
  `(cons ,(second form) nil))

(defmethod normalize-host-operation ((operator (eql 'sb-impl::xsubtract)) form)
  (declare (ignore operator))
  (let ((delta (gensym "DELTA")) (old (gensym "OLD")))
    `(let ((,delta ,(second form)) (,old ,(third form))) (- ,old ,delta))))

(defmethod normalize-host-operation ((operator (eql 'sb-kernel:the*)) form)
  (declare (ignore operator))
  `(the ,(first (second form)) ,(third form)))

(defmethod normalize-host-operation ((operator (eql 'sb-ext:truly-the)) form)
  (declare (ignore operator))
  `(the ,(second form) ,(third form)))

(defmethod normalize-host-operation ((operator (eql 'sb-kernel:%puthash)) form)
  (declare (ignore operator))
  (let ((key (gensym "KEY")) (table (gensym "TABLE")) (value (gensym "VALUE")))
    `(let ((,key ,(second form)) (,table ,(third form)) (,value ,(fourth form)))
       (setf (gethash ,key ,table) ,value))))

(defmethod normalize-host-operation ((operator (eql 'sb-kernel:ecase-failure)) form)
  (declare (ignore operator))
  `(error 'type-error :datum ,(second form) :expected-type (cons 'member ,(third form))))
