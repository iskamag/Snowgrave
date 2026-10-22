(in-package #:snowgrave.tests)

(defvar *callable-retention-sequence* 0)

(defun callable-retention-case (tag definitions body &key refusal (expected '(17))
                                                  (policy :entries) actual-only
                                                  (operation-body "(slot-value object 'data)"))
  (let* ((index (incf *callable-retention-sequence*))
         (package (make-package (format nil "SNOWGRAVE.CALLABLE.RETENTION.~D" index) :use '("CL")))
         (*package* package)
         (forms (read-from-string
                 (format nil "((defclass holder () ((data :initarg :data)))
                                (defgeneric operation (object))
                                (defmethod operation ((object holder)) ~A)
                                ~A
                                (defun entry (object) (declare (ignorable object)) ~A))"
                         operation-body definitions body)))
         (holder (intern "HOLDER" package)) (entry (intern "ENTRY" package))
         (generics (remove-duplicates
                    (loop for form in forms when (member (car form) '(defgeneric defmethod))
                          collect (second form)) :test #'equal)))
    (dolist (form forms) (eval form))
    (let* ((root (make-instance holder :data 17)) (unit nil)
           (condition (handler-case
                          (progn
                            (setf unit (snowgrave:close-source-unit
                                        (list :forms forms) :unit-name (list :callable-retention tag index)
                                        :closed-classes (list holder) :universe (list holder 'number t)
                                        :closed-generics generics :entries (list entry)
                                        :deployment-roots policy
                                        :external-domains (list (list entry (list (list 'eql root))))))
                            nil)
                        (snowgrave:snowgrave-error (condition) condition))))
      (if refusal
          (progn
            (check (typep condition 'snowgrave:snowgrave-error))
            (unless (eq refusal (snowgrave:error-feature condition))
              (error "~S expected ~S, got ~A" tag refusal condition))
            (check (eq refusal (snowgrave:error-feature condition))))
          (progn
            (when condition (error "~S unexpectedly refused: ~A" tag condition))
            (check (null condition))
            (check (eq (if (eq policy :entries)
                           :sealed-partition-minus-proved-unreachable-cells
                           :whole-sealed-partition-of-each-retained-generic)
                       (getf (getf (snowgrave:unit-metadata unit) :deployment) :cell-coverage)))
            (when actual-only
              (let* ((flow (getf (snowgrave:unit-metadata unit) :ordinary-function-flow))
                     (key (snowgrave::function-name-key (intern "OPERATION" package)))
                     (row (find key (getf flow :generic-call-bindings) :key (lambda (row) (getf row :generic-key))
                                :test #'equal))
                     (shapes (getf row :raw-call-shapes)))
                (check (member key (getf flow :retained-named-values) :test #'equal))
                (check shapes)
                (check (every (lambda (row) (not (first (first row)))) shapes))))
            (check (equal expected (multiple-value-list (funcall entry (make-instance holder :data 17)))))
            (check (equal expected (multiple-value-list
                                    (funcall (snowgrave:unit-function unit entry :bind-configuration t))))))))))

(defun callable-retention-tests ()
  (callable-retention-case :ignored-identity ""
   "(let ((saved #'operation)) (declare (ignore saved)) 17)" :operation-body "17")
  (callable-retention-case :self-identity ""
   "(eq #'operation #'operation)" :operation-body "17" :expected '(t))
  (callable-retention-case :identity-body-still-audited
   "(defun callback (object) (declare (ignore object)) (not-a-declared-operation 0))"
   "(let ((saved #'callback)) (declare (ignore saved)) 17)"
   :operation-body "17" :refusal :call-target)
  (callable-retention-case :identity-private-state-still-audited ""
   "(let ((saved #'operation)) (declare (ignore saved)) 17)"
   :refusal :graph-state-slot-read)
  (callable-retention-case :lexical-alias
   "(defun run (object callback) (let ((saved callback)) (funcall saved object)))"
   "(run object #'operation)" :actual-only t)
  (callable-retention-case :default
   "(defun run (object &optional (callback #'operation)) (funcall callback object))"
   "(run object)")
  (callable-retention-case :ordinary-target
   "(defun callback (object) (slot-value object 'data))
    (defun run (object callback) (funcall callback object))"
   "(run object #'callback)")
  (callable-retention-case :scalar-recursion
   "(defun run (object callback count)
      (if (zerop count) (funcall callback object) (run object callback (1- count))))"
   "(run object #'operation 2)")
  ;; A named callable returned by the default's helper is independent of
  ;; record-state snapshots, so it retains the same finite invocation proof.
  (callable-retention-case :helper-default-target
   "(defmethod operation ((object number)) (class-of object))
    (defun target () #'operation)
    (defun run (object &optional (callback (target))) (funcall callback object))"
   "(run object)" :actual-only t)
  ;; Finite defaults, helper returns and a method/helper recursive component
  ;; revisit cells after an earlier scratch omission.
  (callable-retention-case :finite-default-target
   "(defmethod operation ((object number)) (class-of object))
    (defun run (object &optional (callback #'operation)) (funcall callback object))"
   "(run object)")
  (callable-retention-case :late-helper-return
   "(defmethod operation ((object number)) (class-of object))
    (defun identity-through-call (object) object)
    (defun run (object callback) (funcall callback (identity-through-call object)))"
   "(run object #'operation)")
  (callable-retention-case :recursive-method-component
   "(defmethod operation ((object number)) (class-of object))
    (defgeneric recur (object count))
    (defmethod recur ((object holder) count)
      (if (zerop count) (operation object) (again object (1- count))))
    (defmethod recur ((object number) count)
      (declare (ignore count)) (class-of object))
    (defun again (object count) (recur object count))"
   "(recur object 2)")
  (callable-retention-case :late-numeric-caller
   "(defmethod operation ((object number)) (class-of object))
    (defun numeric () 0)
    (defun run (object callback) (funcall callback object))"
   "(run object #'operation) (run (numeric) #'operation)"
   :refusal 'class-of)
  ;; The general profile retains its existing arbitrary-capture obligation.
  (callable-retention-case :selected-profile
   "(defun run (object callback) (funcall callback object))"
   "(run object #'operation)" :policy :selected :refusal :graph-state-slot-read)
  (callable-retention-case :public-return "(defun run (callback) callback)"
   "(run #'operation)" :operation-body "17" :refusal :graph-state-result)
  (callable-retention-case :shared-store
   "(defparameter *saved* nil) (defun run (callback) (setf *saved* callback) 17)"
   "(run #'operation)" :operation-body "17" :refusal :external-shared-state-representation)
  (callable-retention-case :native-aggregate "(defun run (callback) (list callback) 17)"
   "(run #'operation)" :operation-body "17" :refusal :graph-state-operation-input)
  (callable-retention-case :assertion-error
   "(defun run (callback) (the fixnum callback) 17)"
   "(run #'operation)" :operation-body "17" :refusal :private-type-assertion-error)
  (callable-retention-case :declaration-error
   "(defun transport (callback) callback)
    (defun run (callback) (declare (type fixnum callback)) callback 17)"
   "(run (transport #'operation))" :operation-body "17" :refusal :private-type-declaration-error)
  (callable-retention-case :shorthand-declaration-error
   "(defun transport (callback) callback)
    (defun run (callback) (declare (fixnum callback)) callback 17)"
   "(run (transport #'operation))" :operation-body "17" :refusal :private-type-declaration-error)
  (callable-retention-case :declaration-function
   "(defun run (object callback) (declare (type function callback)) (funcall callback object))"
   "(run object #'operation)")
  (callable-retention-case :ordinary-keyword-error
   "(defun parse (&key flag) (declare (ignore flag)) 17)
    (defun run (callback) (parse callback 17))"
   "(run #'operation)" :operation-body "17" :refusal :graph-state-parser-payload)
  (callable-retention-case :generic-keyword-error
   "(defgeneric parse (value &key flag))
    (defmethod parse ((value t) &key flag) (declare (ignore value flag)) 17)
    (defun run (callback) (parse 0 callback 17))"
   "(run #'operation)" :operation-body "17" :refusal :graph-state-parser-payload)
  (callable-retention-case :apply-tail-error
   "(defun parse (value) (declare (ignore value)) 17)
    (defun run (callback) (apply #'parse 0 callback))"
   "(run #'operation)" :operation-body "17" :refusal :graph-state-apply-tail)
  (callable-retention-case :generic-error-ingress
   "(defun run (object callback) (funcall callback object))"
   "(run object #'operation) (operation) 17" :refusal :graph-state-generic-authority)
  ;; A leaked callable's result/effect boundary matters independently of its
  ;; input proof. Do not expose even a universally callable fresh-record maker.
  (callable-retention-case :generic-error-private-result
   "(defgeneric maker (value))
    (defmethod maker ((value t)) (declare (ignore value)) (make-instance 'holder :data 23))"
   "(maker) 17" :refusal :graph-state-generic-authority)
  (callable-retention-case :no-applicable-method
   "(defgeneric parse (value))
    (defmethod parse ((value number)) (declare (ignore value)) 17)"
   "(parse object) 17" :refusal :graph-state-generic-authority)
  (callable-retention-case :no-next-method "" "(operation object)"
   :operation-body "(call-next-method)" :refusal :graph-state-generic-authority))

(defun independent-callable-result-tests ()
  (callable-retention-case :helper-default-union
   "(defun other (object) (slot-value object 'data))
    (defun target (flag) (if flag #'operation #'other))
    (defun run (object flag &optional (callback (target flag))) (funcall callback object))"
   "(values (run object t) (run object nil))" :expected '(17 17))
  (callable-retention-case :helper-default-effects
   "(defun target () #'operation)
    (defun run (object &optional (callback (target)))
      (values (funcall callback object) (slot-value object 'data)))"
   "(run object)" :operation-body "(setf (slot-value object 'data) 23)"
   :expected '(23 23))
  (callable-retention-case :helper-default-setf-target
   "(defgeneric (setf data) (value object))
    (defmethod (setf data) (value (object holder)) (setf (slot-value object 'data) value))
    (defun target () #'(setf data))
    (defun run (object &optional (callback (target)))
      (funcall callback 23 object) (slot-value object 'data))"
   "(run object)" :expected '(23))
  (callable-retention-case :helper-default-mvc-secondary
   "(defun target () #'operation)
    (defun pair (first second) (values first second))
    (defun run (object &optional (callback (target)))
      (multiple-value-call #'pair (funcall callback object)))"
   "(run object)" :operation-body "(values (slot-value object 'data) :ok)" :expected '(17 :ok))
  (callable-retention-case :helper-default-mvc-order
   "(defun target () #'operation)
    (defun triple (first second third) (values first second third))
    (defun run (object &optional (callback (target)))
      (multiple-value-call #'triple (values :head) (funcall callback object)))"
   "(run object)" :operation-body "(values (slot-value object 'data) :ok)" :expected '(:head 17 :ok))
  (callable-retention-case :helper-default-mvc-zero
   "(defun target () #'operation)
    (defun zero () 17)
    (defun run (object &optional (callback (target)))
      (multiple-value-call #'zero (funcall callback object)))"
   "(run object)" :operation-body "(values)" :expected '(17))
  (callable-retention-case :helper-default-mvc-prefix-effect
   "(defun target () #'operation)
    (defun triple (first second third) (values first second third))
    (defun run (object &optional (callback (target)))
      (multiple-value-call #'triple
        (progn (setf (slot-value object 'data) 19) (values :head))
        (funcall callback object)))"
   "(run object)" :operation-body "(values (slot-value object 'data) :ok)" :expected '(:head 19 :ok))
  (callable-retention-case :helper-default-mvc-variable-count
   "(defun other (object) (declare (ignore object)) (values 17 :ok :extra))
    (defun target (flag) (if flag #'operation #'other))
    (defun pair (first second) (values first second))
    (defun run (object flag &optional (callback (target flag)))
      (multiple-value-call #'pair (funcall callback object)))"
   "(run object t) (run object nil)"
   :operation-body "(values 17 :ok)" :refusal :multiple-value-arguments)
  ;; Independent identity never means native data or publication authority.
  (dolist (spec '((:result "callback" :graph-state-result)
                  (:aggregate "(list callback) 17" :graph-state-operation-input)
                  (:assertion "(the fixnum callback) 17" :private-type-assertion-error)
                  (:declaration "(locally (declare (type (and function (not compiled-function)) callback))
                                    (funcall callback object))" :private-type-declaration-error)
                  (:short-call "(funcall callback) 17" :graph-state-generic-authority)))
    (callable-retention-case
     (list :helper-default-boundary (first spec))
     (format nil "(defun target () #'operation)
                  (defun run (object &optional (callback (target)))
                    (declare (ignorable object)) ~A)" (second spec))
     "(run object)" :operation-body "17" :refusal (third spec)))
  (callable-retention-case :helper-default-late-unsafe-caller
   "(defmethod operation ((object number)) (class-of object))
    (defun target () #'operation)
    (defun run (object &optional (callback (target))) (funcall callback object))"
   "(run object) (run 0) 17" :refusal 'class-of)
  (callable-retention-case :helper-default-unsolved-component
   "(defun target () (target))
    (defun run (object &optional (callback (target))) (funcall callback object))"
   "(run object)" :operation-body "17" :refusal :computed-function)
  (callable-retention-case :helper-default-mixed-target
   "(defun target (flag object) (if flag #'operation object))
    (defun run (object flag &optional (callback (target flag object))) (funcall callback object))"
   "(run object t) (run object nil) 17" :operation-body "17" :refusal :computed-function))

(defun callable-retention-dormant-tests ()
  ;; The complete caller proof can omit a cell, including one sharing its
  ;; method with the live subclass. A real caller must restore its obligation.
  (dolist (disjoint '(nil t))
   (dolist (bad-caller '(nil t))
    (let* ((*package* (make-package (format nil "SNOWGRAVE.CALLABLE.DORMANT.~S.~S" disjoint bad-caller) :use '("CL")))
           (forms (read-from-string
                   (format nil "((defclass base () ((data :initarg :data)))
                                 (defclass child ~A ~A)
                                 (defclass roots () ((live :initarg :live) (dormant :initarg :dormant)))
                                 (defgeneric operation (object))
                                 (defmethod operation ((object base)) (slot-value object 'data)) ~A
                                 (defun run (object callback) (funcall callback object))
                                 (defun entry (root) (run (slot-value root '~A) #'operation)))"
                           (if disjoint "()" "(base)") (if disjoint "((data :initarg :data))" "()")
                           (if disjoint "(defmethod operation ((object child)) (slot-value object 'data))" "")
                           (if bad-caller "dormant" "live")))))
      (dolist (form forms) (eval form))
      (let* ((root (make-instance (intern "ROOTS")
                                  :live (make-instance (intern "CHILD") :data 17)
                                  :dormant (make-instance (intern "BASE"))))
             (unit nil)
             (condition (handler-case
                            (progn (setf unit (snowgrave:close-source-unit
                             (list :forms forms) :unit-name (list :callable-dormant disjoint bad-caller)
                             :closed-classes (mapcar #'intern '("BASE" "CHILD" "ROOTS"))
                             :closed-generics (list (intern "OPERATION"))
                             :universe (append (mapcar #'intern '("BASE" "CHILD" "ROOTS")) '(t))
                             :entries (list (intern "ENTRY")) :deployment-roots :entries
                             :external-domains (list (list (intern "ENTRY") (list (list 'eql root)))))) nil)
                          (snowgrave:snowgrave-error (condition) condition))))
        (if bad-caller
            (progn
              (check (handler-case (progn (funcall (intern "ENTRY") root) nil) (unbound-slot () t)))
              (check (typep condition 'snowgrave:snowgrave-error))
              (unless (eq :graph-state-slot-read (snowgrave:error-feature condition))
                (error "Dormant real caller expected private slot refusal, got ~A" condition))
              (check (eq :graph-state-slot-read (snowgrave:error-feature condition))))
            (progn
              (check (= 17 (funcall (intern "ENTRY") root)))
              (when condition (error "Dormant-cell proof refused: ~A" condition))
              (check (= 17 (funcall (snowgrave:unit-function unit (intern "ENTRY") :bind-configuration t))))
              (let* ((dispatch (getf (snowgrave:unit-metadata unit) :dispatch))
                     (operation (find (intern "OPERATION") dispatch :key (lambda (row) (getf row :generic)))))
                (check (some (lambda (cell)
                               (and (equal (getf cell :classes) (list (intern "BASE")))
                                    (eq (getf cell :behavior) :unreachable-from-admitted-calls)
                                    (eq (getf cell :proof) :settled-ordered-call-inputs)))
                             (getf operation :cells)))))))))))
