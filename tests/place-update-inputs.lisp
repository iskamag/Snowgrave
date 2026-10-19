(in-package #:snowgrave.tests)

(defun place-update-input-tests ()
  ;; These are defined native TYPE-ERROR paths, not typed-slot violations.
  ;; The old capture policy already accepts the arbitrary-safe callback.
  (dolist (policy '(:selected :entries))
    (dolist (operator '(incf decf pop))
      (callable-payload-case operator
       (format nil "(let ((callback (transport #'operation))) (~A callback) 17)" operator)
       :type "t" :policy policy :extra "(defun transport (value) value)"
       :refusal :graph-state-update-input)))
  (callable-payload-case :delta
   "(let ((value 17)) (incf value (transport #'operation)) 17)"
   :type "t" :extra "(defun transport (value) value)" :refusal :graph-state-update-input)
  (dolist (body '("(let ((value 17))
                    (setf value (if (snowgrave.tests::callable-payload-choice) #'operation 17)) (incf value) 17)"
                  "(let ((value 17)) (let ((value (transport #'operation))) (incf value)) 17)"
                  "(let ((value 17)) (dotimes (index 2)
                       (when (eql index 1)
                         (setf value (if (snowgrave.tests::callable-payload-choice) #'operation 17)))
                       (incf value)) 17)"
                  "(setf (slot-value object 'data) 17)
                   (incf (slot-value object 'data)
                         (progn (setf (slot-value object 'data) #'operation) 1)) 17"
                  "(setf (slot-value object 'data) #'operation)
                   (incf (slot-value object 'data)
                         (prog1 (slot-value object 'data) (setf (slot-value object 'data) 17))) 17"))
    (callable-payload-case :changed-input body :type "t" :refusal :graph-state-update-input
     :extra "(defun transport (value) value)"))
  (callable-payload-case :unbound-reader
   "(slot-makunbound object 'data) (incf (slot-value object 'data)) 17"
   :type "t" :refusal :graph-state-slot-read)
  (callable-payload-case :getter-effects
   "(setf (slot-value object 'data) 17) (incf (cell object)) 17" :type "t"
   :extra "(defun cell (object)
             (prog1 (slot-value object 'data) (slot-makunbound object 'data)))
           (defun (setf cell) (value object)
             (slot-value object 'data) (setf (slot-value object 'data) value))"
   :refusal :graph-state-slot-read)
  (dolist (operator '(push pushnew))
    (callable-payload-case operator
     (format nil "(let ((values nil)) (~A (transport #'operation) values) 17)" operator)
     :type "t" :extra "(defun transport (value) value)" :refusal :graph-state-update-input)
    (callable-payload-case :tail
     (format nil "(let ((values (transport #'operation))) (~A 17 values) 17)" operator)
     :type "t" :extra "(defun transport (value) value)" :refusal :graph-state-update-input))
  (callable-payload-case :incf-native
   "(let ((value (transport 17))) (eql (incf value) 18))" :type "t"
   :extra "(defun transport (value) value)" :expected '(t))
  (callable-payload-case :decf-native
   "(let ((value (transport 17))) (eql (decf value) 16))" :type "t"
   :extra "(defun transport (value) value)" :expected '(t))
  (callable-payload-case :pop-native
   "(let ((value '(17))) (eql (pop value) 17))" :type "t" :expected '(t))
  (callable-payload-case :push-native
   "(let ((values nil)) (push 17 values) 17)" :type "t" :expected '(17)))
