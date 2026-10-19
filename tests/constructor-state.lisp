(in-package #:snowgrave.tests)

(defvar *constructor-state-sequence* 0)
(defvar *constructor-state-events* nil)
(defun constructor-state-event (tag) (push tag *constructor-state-events*) nil)
(defun constructor-state-opaque (class) (make-instance class))
(defun constructor-state-read (package text)
  (let ((*package* package)) (read-from-string text)))
(defun constructor-state-observation (function mapping)
  (let ((*constructor-state-events* nil))
    (handler-case
        (list :values (multiple-value-list (funcall function)) :events (reverse *constructor-state-events*))
      (error (condition)
        (list :error (condition-observation condition mapping) :events (reverse *constructor-state-events*))))))

(defun constructor-state-case (tag definitions body expected
                               &key refusal protocol external-operations (native-expected nil native-expected-p))
  ;; Separate native/installed roots and unique authored classes prevent a
  ;; native mutation or an earlier fixture method from changing admission.
  (let* ((index (incf *constructor-state-sequence*))
         (package (make-package (format nil "SNOWGRAVE.CONSTRUCTOR.STATE.~D" index) :use '("CL")))
         (forms (append (constructor-state-read package "((defclass anchor () ((data :initarg :data))))")
                        (constructor-state-read package definitions)
                        (constructor-state-read package (format nil "((defun entry (root) ~A))" body))))
         (classes (loop for form in forms when (eq (first form) 'defclass) collect (second form)))
         (generics (remove-duplicates
                    (loop for form in forms when (member (first form) '(defgeneric defmethod)) collect (second form))
                    :test #'equal))
         (entry (intern "ENTRY" package)))
    (dolist (form forms) (eval form))
    (when (or protocol (intersection generics '(initialize-instance shared-initialize)))
      (pushnew 'initialize-instance generics) (pushnew 'shared-initialize generics))
    (let* ((native-root (make-instance (intern "ANCHOR" package) :data (vector nil 17)))
           (installed-root (make-instance (intern "ANCHOR" package) :data (vector nil 17)))
           (identity (list :constructor-state tag index))
           (unit nil)
           (condition
             (handler-case
                 (progn
                   (when native-expected-p
                     (check (equal native-expected (multiple-value-list (funcall entry native-root)))))
                   (setf unit (snowgrave:close-source-unit
                               (list :forms forms) :unit-name identity :closed-classes classes
                               :closed-generics generics
                               :universe (append classes '(number symbol vector list cons function t))
                               :entries (list entry)
                               :external-domains (list (list entry (list (list 'eql installed-root))))
                               :external-operations (cons 'constructor-state-event external-operations)))
                   nil)
               (snowgrave:snowgrave-error (condition) condition))))
      (if refusal
          (progn (check (typep condition 'snowgrave:snowgrave-error))
                 (when (keywordp refusal) (check (eq refusal (snowgrave:error-feature condition)))))
          (progn
            (check (null condition))
            (let* ((layouts (getf (snowgrave:unit-metadata unit) :record-layouts))
                   (native-map (mapcar (lambda (class) (cons (find-class class) class)) classes))
                   (closed-map (mapcar (lambda (row) (cons (getf row :class-token) (getf row :class))) layouts))
                   (native (constructor-state-observation (lambda () (funcall entry native-root)) native-map))
                   (closed (constructor-state-observation
                            (snowgrave:unit-function unit entry :bind-configuration t) closed-map)))
              (check (equal native closed))
              (when expected (check (equal expected (getf closed :values))))
              (check (not (search ":OWNED-RECORD"
                                  (with-output-to-string (stream) (snowgrave:write-unit-source unit stream)))))))))))

(defun constructor-state-tests ()
  (constructor-state-case :identity "((defclass node () ()))"
    "(let ((a (make-instance 'node)) (b (make-instance 'node)))
       (values (typep a 'node) (eq a b) (equalp a b) (eq a root)))" '(t nil nil nil))
  (constructor-state-case :bound-nil "((defclass node () ((data :initform nil))))"
    "(declare (ignore root)) (let ((n (make-instance 'node)))
       (values (slot-boundp n 'data) (slot-value n 'data)))" '(t nil))
  (constructor-state-case :retained-parent "((defclass node () ((parent :initarg :parent))))"
    "(eq root (slot-value (make-instance 'node :parent root) 'parent))" '(t))
  (constructor-state-case :helper-default
    "((defun backing () (vector 17 23))
       (defclass base () ((data :initarg :data)))
       (defclass node (base) () (:default-initargs :data (backing))))"
    "(declare (ignore root)) (length (fill (slot-value (make-instance 'node) 'data) nil))" '(2))
  (constructor-state-case :helper-initform
    "((defun backing () (vector 17 23)) (defclass node () ((data :initform (backing)))))"
    "(declare (ignore root)) (length (fill (slot-value (make-instance 'node) 'data) nil))" '(2))
  (constructor-state-case :duplicate-initargs
    "((defclass node () ((data :initarg :left :initarg :right))))"
    "(declare (ignore root))
     (slot-value (make-instance 'node :right (progn (snowgrave.tests::constructor-state-event :first) 17)
                                    :left (progn (snowgrave.tests::constructor-state-event :second) 23)
                                    :right (progn (snowgrave.tests::constructor-state-event :third) 41)) 'data)" '(17))
  (constructor-state-case :native-invalid-key "((defclass node () ()))"
    "(declare (ignore root)) (typep (make-instance 'node :unknown 17) 'node)" nil)
  (constructor-state-case :abrupt-cleanup
    "((defclass node () ())
       (defmethod initialize-instance :after ((n node) &rest args)
         (declare (ignore n args)) (snowgrave.tests::constructor-state-event :after) (error \"native payload\")))"
    "(declare (ignore root)) (unwind-protect (typep (make-instance 'node) 'node)
       (snowgrave.tests::constructor-state-event :cleanup))" nil)
  (constructor-state-case :recursive-family
    "((defclass node () ((child :initarg :child)))
       (defun tree (depth) (if (zerop depth) (make-instance 'node :child nil)
                             (make-instance 'node :child (tree (1- depth))))))"
    "(declare (ignore root)) (typep (tree 3) 'node)" '(t))
  ;; Every normally returning family profile contributes to boundness.
  (constructor-state-case :mixed-bound-read
    "((defclass node () ((data :initarg :data))))"
    "(declare (ignore root)) (make-instance 'node) (slot-value (make-instance 'node :data nil) 'data)"
    nil :refusal :graph-state-slot-read)
  (constructor-state-case :unbound "((defclass node () ((data))))"
    "(declare (ignore root)) (slot-value (make-instance 'node) 'data)" nil :refusal :graph-state-slot-read)
  (constructor-state-case :private-type-error "((defclass node () ((data :initarg :data :type fixnum))))"
    "(make-instance 'node :data root) 0" nil :refusal :construction-private-type-error)
  (constructor-state-case :private-ignored-key "((defclass node () ()))"
    "(make-instance 'node :unknown root) 0" nil :refusal :construction-private-initarg)
  (constructor-state-case :private-with-invalid-key "((defclass node () ((data :initarg :data))))"
    "(make-instance 'node :data root :unknown 17) 0" nil :refusal :construction-private-keywords)
  (constructor-state-case :malformed-private-args "((defclass node () ((data :initarg :data))))"
    "(make-instance 'node :data root :dangling) 0" nil :refusal :construction-initargs)
  (constructor-state-case :before-phase
    "((defclass node () ((data :initform 17)))
       (defmethod initialize-instance :before ((n node) &rest args)
         (declare (ignore args)) (slot-value n 'data)))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)" nil :refusal :graph-state-slot-read)
  (constructor-state-case :custom-poststate
    "((defclass node () ((data :initform 17)))
       (defmethod initialize-instance :after ((n node) &rest args) (declare (ignore n args))))"
    "(declare (ignore root)) (slot-value (make-instance 'node) 'data)" nil :refusal :graph-state-slot-read)
  (constructor-state-case :selected-other-error
    "((defclass node () ()) (defclass other () ())
       (defmethod initialize-instance :after ((n other) &rest args)
         (declare (ignore args)) (error \"private ~S\" n)))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)" nil :refusal t)
  (constructor-state-case :fresh-the "((defclass node () ()))"
    "(declare (ignore root)) (length (the list (make-instance 'node)))" nil :refusal :private-type-assertion-error)
  (constructor-state-case :captured-the "((defclass node () ()))"
    "(length (the list root))" nil :refusal :private-type-assertion-error)
  (constructor-state-case :mixed-private-native-the "((defclass node () ()))"
    "(null (the list (if (zerop (length (slot-value root 'data)))
                         (snowgrave.tests::constructor-state-opaque 'node)
                         (make-instance 'node))))"
    nil :refusal :private-type-assertion-error
    :external-operations '(constructor-state-opaque))
  (constructor-state-case :secondary "((defclass node () ()))"
    "(declare (ignore root)) (values 17 (make-instance 'node))" nil :refusal :graph-state-result)
  (constructor-state-case :callback-escape "((defclass node () ()))"
    "(declare (ignore root)) (let ((n (make-instance 'node))) #'(lambda () n))" nil :refusal :graph-state-result)
  (constructor-state-case :fresh-container "((defclass node () ()))"
    "(fill (vector (make-instance 'node)) nil :end (length (slot-value root 'data))) 0" nil :refusal :graph-state-operation-input)
  ;; An unrelated reinitialization invalidates DATA value facts globally.
  ;; The field's retained native origin must survive that conservative join.
  (constructor-state-case :retained-opaque-after-reinitialization
    "((defclass marker () ()) (defclass node () ((data :initarg :data))))"
    "(let ((fresh (make-instance 'node :data (snowgrave.tests::constructor-state-opaque 'marker))))
       (shared-initialize root t :data 17) (typep (slot-value fresh 'data) 'marker))"
    nil :refusal :external-result-class-observation :protocol t :native-expected '(t)
    :external-operations '(constructor-state-opaque))
  ;; Explicit initialization is a state transition, including on captured
  ;; nodes. Its writes cannot preserve an earlier backing-vector fact.
  (constructor-state-case :captured-reinitialization "((defclass node () ()))"
    "(shared-initialize root t :data root) (length (fill (slot-value root 'data) nil))"
    nil :refusal t :protocol t)
  (constructor-state-case :fresh-reinitialization "((defclass node () ((data :initarg :data))))"
    "(let ((n (make-instance 'node :data (vector nil))))
       (shared-initialize n t :data root) (length (fill (slot-value n 'data) nil)))"
    nil :refusal t :protocol t))
