(in-package #:snowgrave.tests)

(defun configuration-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :configuration
       "((defclass model () ((value :initform 1 :accessor value)))
          (defclass first-model (model) ())
          (defclass second-model (model) ())
          (defclass collector () ((model :initarg :model :accessor model)))
          (defclass callbacks () ((target :initarg :target :reader callback-target)
                                 (option :initform :key :reader callback-option)))
          (defgeneric advance (model &optional amount))
          (defmethod advance ((model first-model) &optional (amount 2))
            (incf (value model) amount))
          (defmethod advance ((model second-model) &optional (amount 3))
            (incf (value model) amount))
          (defun construct (first)
            (make-instance 'collector :model (make-instance (if first 'first-model 'second-model))))
          (defun run (collector) (advance (model collector)))
          (defun component (collector) (model collector))
          (defun replace-component (collector component) (setf (model collector) component))
          (defun clear-component (collector) (slot-makunbound collector 'model))
          (defun make-callback (function) (make-instance 'callbacks :target function))
          (defun callback (holder) (funcall (callback-target holder)))
          (defun reduce-callback (holder items) (reduce (callback-target holder) items))
          (defun reduce-option (holder) (reduce #'+ '(1 2 3) (callback-option holder) (callback-target holder))))"
       "(construct run component replace-component clear-component make-callback callback reduce-callback reduce-option)"
       "((construct (t)) (run (collector)) (component (collector))
          (replace-component (collector t)) (clear-component (collector)) (make-callback (function))
          (callback (callbacks)) (reduce-callback (callbacks list)) (reduce-option (callbacks)))"
       "(value (setf value) model (setf model) callback-target callback-option advance)")
    (flet ((entry (name) (snowgrave:unit-function unit (find-symbol name package))))
      (let* ((first (funcall (entry "CONSTRUCT") t))
             (second (funcall (entry "CONSTRUCT") nil))
             (roles (fixture-read package "((collector model))"))
             (one (snowgrave:bind-entry unit (find-symbol "RUN" package) (list first) :roles roles))
             (two (snowgrave:bind-entry unit (find-symbol "RUN" package) (list second) :roles roles)))
        (check (= 3 (funcall one)) "First configured method was not selected")
        (check (= 4 (funcall two)) "Second configured method was not selected")
        (check (= 5 (funcall one)) "Later configuration changed an earlier entry")
        (check (= 7 (funcall two)) "Native data did not remain mutable")
        (check (eq :configuration-dispatch
                   (handler-case
                       (progn (snowgrave:bind-entry unit (find-symbol "RUN" package) (list first)) nil)
                     (snowgrave:snowgrave-error (condition) (snowgrave:error-feature condition))))
               "Missing configuration facts did not reject residual dispatch")
        (check (eq :configuration-indirect-call
                   (handler-case
                       (progn (snowgrave:bind-entry unit (find-symbol "CALLBACK" package)
                                                   (list (funcall (entry "MAKE-CALLBACK") (lambda () 17)))) nil)
                     (snowgrave:snowgrave-error (condition) (snowgrave:error-feature condition))))
               "Unknown function-valued call passed the directness audit")
        (check (eq :configuration-indirect-call
                   (handler-case
                       (progn (snowgrave:bind-entry unit (find-symbol "REDUCE-CALLBACK" package)
                                                   (list (funcall (entry "MAKE-CALLBACK") #'+) '(1 2 3))) nil)
                     (snowgrave:snowgrave-error (condition) (snowgrave:error-feature condition))))
               "Unknown native callback passed the directness audit")
        (check (eq :configuration-indirect-call
                   (handler-case
                       (progn (snowgrave:bind-entry unit (find-symbol "REDUCE-OPTION" package)
                                                   (list (funcall (entry "MAKE-CALLBACK") #'1+))) nil)
                     (snowgrave:snowgrave-error (condition) (snowgrave:error-feature condition))))
               "Computed callback keyword passed the directness audit")
        (check (eq :configuration-arguments
                   (handler-case (progn (snowgrave:bind-entry unit (find-symbol "RUN" package) '(7) :roles roles) nil)
                     (snowgrave:snowgrave-error (condition) (snowgrave:error-feature condition))))
               "Binder did not validate the entry's declared root domain")
        (check (handler-case
                   (progn (funcall (entry "REPLACE-COMPONENT") first (funcall (entry "COMPONENT") second)) nil)
                 (error () t))
               "Exposed setter reconfigured a bound collector")
        (check (handler-case (progn (funcall (entry "CLEAR-COMPONENT") first) nil) (error () t))
               "Exposed slot-makunbound unbound a component role")
        (check (handler-case
                   (progn (funcall (entry "REPLACE-COMPONENT") first
                                   (funcall (entry "COMPONENT") (funcall (entry "CONSTRUCT") t))) nil)
                 (error () t))
               "Same-class replacement escaped the sealed component graph")
        (check (= 7 (funcall one)) "Failed reconfiguration damaged the original binding"))))
  (configuration-callback-tests)
  (configuration-slot-error-tests))

(defun configuration-callback-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :configuration-callbacks
       "((defgeneric add (a b))
          (defmethod add ((a integer) (b integer)) (+ a b))
          (defun helper (a b) (add a b))
          (defun direct (items) (reduce #'add items))
          (defun indirect (items) (reduce #'helper items))
          (defun quoted (items) (reduce 'helper items)))"
       "(direct indirect quoted)" "((direct (list)) (indirect (list)) (quoted (list)))"
       "(add)" :universe "(integer)")
    (dolist (name '("DIRECT" "INDIRECT" "QUOTED"))
      (let ((feature
              (handler-case (progn (snowgrave:bind-entry unit (find-symbol name package) '((1 2 3))) nil)
                (snowgrave:snowgrave-error (condition) (snowgrave:error-feature condition)))))
        (check (member feature '(:configuration-dispatch :configuration-indirect-call))
               "Escaping ~A callback passed the directness audit: ~S" name feature)))))

(defun configuration-slot-error-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :configuration-slot-errors
       "((defclass a () ((x :initform 1)))
          (defclass b () ())
          (defclass holder () ((data :initarg :data :accessor data)))
          (defun construct () (make-instance 'holder :data (make-instance 'a)))
          (defun switch (holder) (setf (data holder) (make-instance 'b)))
          (defun entry (holder) (slot-value (data holder) 'x)))"
       "(construct switch entry)" "((construct ()) (switch (holder)) (entry (holder)))"
       "(data (setf data))")
    (let* ((root (funcall (snowgrave:unit-function unit (find-symbol "CONSTRUCT" package))))
           (base (snowgrave:unit-function unit (find-symbol "ENTRY" package)))
           (bound (snowgrave:bind-entry unit (find-symbol "ENTRY" package) (list root)))
           (make-instance (fdefinition 'make-instance)))
      (check (= 1 (funcall bound)) "Unique physical slot read failed")
      (funcall (snowgrave:unit-function unit (find-symbol "SWITCH" package)) root)
      (check (eq (handler-case (funcall base root) (error (condition) (type-of condition)))
                 (handler-case (funcall bound) (error (condition) (type-of condition))))
             "Configured slot failure changed the condition type")
      (check (eq :configuration-allocation
                 (handler-case
                     (progn (snowgrave:bind-entry unit (find-symbol "CONSTRUCT" package) nil) nil)
                   (snowgrave:snowgrave-error (condition) (snowgrave:error-feature condition))))
             "Configured entry admitted new components")
      (check (eq make-instance (fdefinition 'make-instance)) "Binding changed CL:MAKE-INSTANCE"))))
