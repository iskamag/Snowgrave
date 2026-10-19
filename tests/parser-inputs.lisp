(in-package #:snowgrave.tests)

(defvar *parser-input-sequence* 0)
(defvar *parser-input-events* nil)
(defun parser-input-event (value) (push value *parser-input-events*) value)

(defun parser-input-function-payloads (condition)
  ;; Inspect the actual host condition, rather than infer publication from
  ;; the existence of an error. Unknown-key errors retain KEY, not VALUE.
  (when (typep condition 'condition)
    (let ((seen (make-hash-table :test #'eq)) (functions nil))
      (labels ((walk (value)
                 (cond ((functionp value) (pushnew value functions :test #'eq))
                       ((gethash value seen) nil)
                       ((consp value)
                        (setf (gethash value seen) t) (walk (car value)) (walk (cdr value)))
                       ((simple-vector-p value)
                        (setf (gethash value seen) t) (map nil #'walk value)))))
        (dolist (slot (sb-mop:class-slots (class-of condition)))
          (let ((name (sb-mop:slot-definition-name slot)))
            (when (slot-boundp condition name) (walk (slot-value condition name))))))
      functions)))

(defun parser-input-outcome (function)
  (handler-case (list :values (multiple-value-list (funcall function)))
    (error (condition) condition)))

(defun parser-input-case (tag definitions body &key refusal generic native-target
                                                  native-error callable-error events
                                                  (native-argument nil native-argument-p))
  (let* ((index (incf *parser-input-sequence*))
         (package (make-package (format nil "SNOWGRAVE.PARSER.INPUT.~D" index) :use '("CL")))
         (*package* package)
         (forms (read-from-string
                 (format nil "((defclass holder () ((data :initarg :data)))
                               (defun other (value) (declare (ignore value)) 17)
                               ~A
                               (defun invoke (object callback) (declare (ignorable object callback)) ~A)
                               (defun entry (object) (invoke object ~A) 17))"
                         definitions body (if native-argument-p (prin1-to-string native-argument)
                                              (format nil "#'~A" (or native-target 'other))))))
         (holder (intern "HOLDER" package)) (entry (intern "ENTRY" package))
         (other (intern "OTHER" package))
         (generics (if (eq generic :initialization) '(initialize-instance shared-initialize)
                       (when generic (list (intern "OPERATION" package)))))
         (native nil) (native-events nil) (unit nil) (refused nil))
    (dolist (form forms) (eval form))
    (let ((native-root (make-instance holder :data 17))
          (root (make-instance holder :data 17)))
      (let ((*parser-input-events* nil))
        (setf native (parser-input-outcome (lambda () (funcall entry native-root)))
              native-events (reverse *parser-input-events*)))
      (when native-error (check (typep native native-error)))
      (when callable-error
        (check (member (fdefinition (or native-target other))
                       (parser-input-function-payloads native) :test #'eq)))
      (handler-case
          (setf unit (snowgrave:close-source-unit
                      (list :forms forms) :unit-name (list :parser-input tag index)
                      :closed-classes (list holder) :closed-generics generics
                      :universe (list holder t 'number) :entries (list entry)
                      :deployment-roots :entries
                      :external-domains (list (list entry (list (list 'eql root))))
                      :external-operations '(parser-input-event)))
        (snowgrave:snowgrave-error (condition) (setf refused condition)))
      (cond (refusal
             (unless (and refused (eq refusal (snowgrave:error-feature refused)))
               (error "~S expected ~S, got ~A" tag refusal refused))
             (check (eq refusal (snowgrave:error-feature refused)))
             (check (not (null (snowgrave:error-source-key refused)))))
            (t
             (when refused (error "~S unexpectedly refused: ~A" tag refused))
             (check (null refused))
             (let* ((*parser-input-events* nil)
                    (closed (parser-input-outcome (snowgrave:unit-function unit entry :bind-configuration t))))
               (check (equal native-events (reverse *parser-input-events*)))
               (check (equal events native-events))
               (if native-error
                   (progn
                     (check (eq (type-of native) (type-of closed)))
                     (check (equal (parser-input-function-payloads native)
                                   (parser-input-function-payloads closed))))
                   (check (equal native closed)))))))))

(defun parser-input-tests ()
  (let ((ordinary "(defun operation (object &key flag) (declare (ignore object flag)) 17)")
        (generic "(defgeneric operation (object &key flag))
                  (defmethod operation ((object t) &key flag) (declare (ignore object flag)) 17)"))
    ;; The same raw parser owner serves ordinary, scoped, literal and selected
    ;; generic calls. The malformed names must survive binding projection.
    (dolist (kind '(nil t))
      (let ((definition (if kind generic ordinary)))
        (dolist (call '("(operation 0 callback 17)"
                        "(funcall #'operation 0 callback 17)"
                        "(apply #'operation 0 callback 17 nil)"
                        "(multiple-value-call #'operation (values 0 callback 17))"))
          (parser-input-case :malformed-callable definition call :generic kind
           :refusal :graph-state-parser-payload :native-error 'program-error :callable-error t))
        (parser-input-case :private-record-key definition "(operation 0 object 17)" :generic kind
         :refusal :graph-state-parser-payload :native-error 'program-error)
        (parser-input-case :recognized-value definition "(operation 0 :flag callback)" :generic kind)
        (parser-input-case :recognized-record-value definition "(operation 0 :flag object)" :generic kind)
        (parser-input-case :allow definition "(operation 0 callback 17 :allow-other-keys t)" :generic kind)
        (parser-input-case :first-allow-true definition
         "(operation 0 :allow-other-keys t callback 17 :allow-other-keys nil)" :generic kind)
        (parser-input-case :first-allow-false definition
         "(operation 0 :allow-other-keys nil callback 17 :allow-other-keys t)" :generic kind
         :refusal :graph-state-parser-payload :native-error 'program-error :callable-error t)
        ;; Native callable identity is unchanged, so its actual error is safe.
        (parser-input-case :native-key definition "(operation 0 callback 17)" :generic kind
         :native-target 'car :native-error 'program-error :callable-error t)
        ;; Keep the callee deployed first: a missing target must not mask
        ;; APPLY's own VALUES-LIST-ARGUMENT-ERROR payload exposure. AOK does
        ;; not admit a private tail object, independently of callee parsing.
        (parser-input-case :malformed-tail definition
         "(operation 0 :flag 17) (apply #'operation 0 callback)" :generic kind
         :refusal :graph-state-apply-tail :native-error 'type-error :callable-error t)
        (parser-input-case :native-callable-tail definition
         "(operation 0 :flag 17) (apply #'operation 0 callback)" :generic kind
         :native-target 'car :native-error 'type-error :callable-error t)
        (parser-input-case :native-scalar-tail definition
         "(operation 0 :flag 17) (apply #'operation 0 callback)" :generic kind
         :native-argument 23 :native-error 'type-error)
        (parser-input-case :malformed-tail-allow definition
         "(operation 0 :flag 17) (apply #'operation 0 :allow-other-keys t callback)" :generic kind
         :refusal :graph-state-apply-tail :native-error 'type-error :callable-error t)))
    ;; The payload belongs to the actual value point. An initial NIL field
    ;; cannot justify a later function write, and clearing after a PROG1 read
    ;; cannot erase the already saved operand. Keep the target deployed first.
    (dolist (kind '(nil t))
      (let ((definition (if kind generic ordinary)))
        (loop for body in '("(operation 0 :flag 17) (setf (slot-value object 'data) nil)
                         (apply #'operation 0
                           (progn (setf (slot-value object 'data) #'other) (slot-value object 'data)))"
                        "(operation 0 :flag 17) (setf (slot-value object 'data) #'other)
                         (apply #'operation 0
                           (prog1 (slot-value object 'data) (setf (slot-value object 'data) nil)))"
                        "(operation 0 :flag 17) (setf (slot-value object 'data) nil)
                         (apply #'operation (progn (setf (slot-value object 'data) #'other) 0)
                           (slot-value object 'data))")
              for index from 0 do
          (parser-input-case :tail-value-point definition body :generic kind
           :refusal (if (and kind (< index 2)) :external-result-dispatch :graph-state-apply-tail)
           :native-error 'type-error :callable-error t))
        (dolist (body '("(setf (slot-value object 'data) nil)
                         (operation 0 (progn (setf (slot-value object 'data) #'other)
                                             (slot-value object 'data)) 17)"
                        "(setf (slot-value object 'data) #'other)
                         (operation 0 (prog1 (slot-value object 'data)
                                            (setf (slot-value object 'data) nil)) 17)"))
          (parser-input-case :key-value-point definition body :generic kind
           :refusal :graph-state-parser-payload
           :native-error 'program-error :callable-error t))))
    (dolist (body '("(flet ((operation (value &key flag) (declare (ignore value flag)) 17))
                       (operation 0 callback 17))"
                    "(labels ((operation (value &key flag) (declare (ignore value flag)) 17))
                       (funcall #'operation 0 callback 17))"
                    "(funcall #'(lambda (value &key flag) (declare (ignore value flag)) 17) 0 callback 17)"
                    "(apply #'(lambda (value &key flag) (declare (ignore value flag)) 17) 0 callback 17 nil)"
                    "(multiple-value-call #'(lambda (value &key flag) (declare (ignore value flag)) 17)
                       (values 0 callback 17))"))
      (parser-input-case :scoped-key "" body :refusal :graph-state-parser-payload
       :native-error 'program-error :callable-error t))
    (parser-input-case :optional-prefix
     "(defun operation (value &optional optional &key flag) (declare (ignore value optional flag)) 17)"
     "(operation 0 callback :flag 17)")
    (parser-input-case :method-added-key
     "(defgeneric operation (value &key flag))
      (defmethod operation ((value t) &key flag ((extra provided))) (declare (ignore value flag provided)) 17)"
     "(operation 0 'extra callback)" :generic t)
    (parser-input-case :method-allows
     "(defgeneric operation (value &key flag))
      (defmethod operation ((value t) &key flag &allow-other-keys) (declare (ignore value flag)) 17)"
     "(operation 0 callback 17)" :generic t)
    ;; Cell admission uses ordered actual caller rows. The numeric call does
    ;; not execute the universal cell's stricter parser, while the symbol call
    ;; cannot borrow the numeric method's ALLOW-OTHER-KEYS.
    (let ((methods "(defgeneric operation (value &key flag))
                    (defmethod operation ((value number) &key flag &allow-other-keys)
                      (declare (ignore value flag)) 17)
                    (defmethod operation ((value t) &key flag) (declare (ignore value flag)) 17)"))
      (parser-input-case :applicable-allows methods "(operation 0 callback 17)" :generic t)
      (parser-input-case :inapplicable-allows methods "(operation 'ordinary callback 17)" :generic t
       :refusal :graph-state-parser-payload :native-error 'program-error :callable-error t))
    (parser-input-case :capture-is-not-a-call generic
     "(let ((captured #'operation)) (declare (ignore captured)) 17)" :generic t)
    (parser-input-case :rest-only
     "(defgeneric operation (value &rest arguments))
      (defmethod operation ((value t) &key flag) (declare (ignore value flag)) 17)"
     "(operation 0 callback 17)" :generic t)
    ;; A native odd-count error is selected before key validation and carries
    ;; neither a relocated KEY nor VALUE. Ordinary statically odd calls retain
    ;; their existing compiler refusal; the generic has a runnable host check.
    (dolist (body '("(operation 0 callback 17 :bogus)" "(operation 0 :flag callback :bogus)"))
      (parser-input-case :odd-tail generic body :generic t :native-error 'program-error))
    (parser-input-case :native-key-error generic "(operation 0 :bogus callback)"
     :generic t :native-error 'program-error)
    (parser-input-case :evaluation-order generic
     "(unwind-protect
          (operation (progn (snowgrave.tests::parser-input-event 0) 0)
                     :bogus (progn (snowgrave.tests::parser-input-event 1) callback))
        (snowgrave.tests::parser-input-event 2))"
     :generic t :native-error 'program-error :events '(0 1 2))
    ;; Dynamic source initialization names remain outside the literal-name
    ;; fragment. Its separate emitter cannot authorize these raw operands.
    (dolist (call '("(initialize-instance object callback 17)"
                    "(funcall #'initialize-instance object callback 17)"
                    "(apply #'initialize-instance object (list callback 17))"
                    "(multiple-value-call #'initialize-instance (values object callback 17))"
                    "(shared-initialize object nil callback 17)"))
      (parser-input-case :initialization
       "(defmethod initialize-instance :after ((object holder) &key) (declare (ignore object)))"
       call :generic :initialization :refusal :initialization-argument-shape))
    (dolist (kind '(nil t))
      (let ((definition (if kind
                            "(defgeneric operation (value &key flag &allow-other-keys))
                             (defmethod operation ((value t) &key flag &allow-other-keys) (declare (ignore value flag)) 17)"
                            "(defun operation (value &key flag &allow-other-keys) (declare (ignore value flag)) 17)")))
        (parser-input-case :contract-allows-malformed-tail definition "(operation 0 :flag 17) (apply #'operation 0 callback)"
         :generic kind :refusal :graph-state-apply-tail :native-error 'type-error :callable-error t)))))
