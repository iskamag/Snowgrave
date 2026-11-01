(in-package #:snowgrave.tests)

(defmacro combination-syntax-probe (&rest forms)
  ;; Both the operator and a lexical macro must see actual CALL-METHOD syntax,
  ;; before the closer replaces method objects with ordinary function calls.
  `(macrolet ((method-leaf-p (form) (eq (first form) 'call-method)))
     (values ,(every (lambda (form) (eq (first form) 'call-method)) forms)
             (method-leaf-p ,(first forms)) ,(first forms))))

(defun short-combination-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :short-combinations
       "((define-method-combination collect :operator list :documentation \"Collect primary values.\")
          (define-method-combination single :operator list :identity-with-one-argument t)
          (defgeneric gather (x) (:method-combination collect))
          (defmethod gather collect ((x number)) (values :number :discarded))
          (defmethod gather collect ((x integer)) :integer)
          (defmethod gather :around ((x number))
            (values (call-next-method) :around))
          (defgeneric reversed (x) (:method-combination collect :most-specific-last))
          (defmethod reversed collect ((x number)) :number)
          (defmethod reversed collect ((x integer)) :integer)
          (defgeneric one (x) (:method-combination single))
          (defmethod one single ((x number)) x)
          (define-method-combination choose :operator or)
          (defgeneric choose-value (x) (:method-combination choose))
          (defmethod choose-value choose ((x integer))
            (snowgrave.tests::note-event :integer) nil)
          (defmethod choose-value choose ((x number))
            (snowgrave.tests::note-event :number) (values :found :secondary))
          (defconstant +initial+ (gather 1))
          (defun forward (x) (gather x))
          (defun backward (x) (reversed x))
          (defun identity-entry (x) (one x))
          (defun short-circuit (x) (choose-value x))
          (defun initialized () +initial+))"
       "(forward backward identity-entry short-circuit initialized)"
       "((forward (number)) (backward (number)) (identity-entry (number)) (short-circuit (number)) (initialized ()))"
       "(gather reversed one choose-value)" :universe "(number integer)" :external '(note-event))
    (dolist (row '(("FORWARD" (1) (((:integer :number) :around) nil))
                   ("FORWARD" (1/2) (((:number) :around) nil))
                   ("BACKWARD" (1) (((:number :integer)) nil))
                   ("IDENTITY-ENTRY" (7) ((7) nil))
                   ("SHORT-CIRCUIT" (1) ((:found :secondary) (:integer :number)))
                   ("INITIALIZED" () (((:integer :number)) nil))))
      (destructuring-bind (name arguments expected) row
        (compare-entry unit package name arguments expected)
        (check (equal expected (observed-call
                               (snowgrave:bind-entry unit (find-symbol name package) arguments) nil))
               "Configured short combination differs: ~A" name)))
    (check (eq snowgrave::*composition-source* :inactive)
           "Open-stage initialization retained disposable composition methods")))

(defun combination-macro-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :combination-macro
       "((define-method-combination syntax :operator snowgrave.tests::combination-syntax-probe)
          (defgeneric gather (x) (:method-combination syntax))
          (defmethod gather syntax ((x number)) :number)
          (defmethod gather syntax ((x integer)) :integer)
          (defmethod gather :around ((x number)) (call-next-method))
          (defun entry (x) (gather x)))"
       "(entry)" "((entry (integer)))" "(gather)" :universe "(number integer)")
    (compare-entry unit package "ENTRY" '(1) '((t t :integer) nil))
    (check (equal '(t t :integer)
                  (multiple-value-list (funcall (snowgrave:bind-entry unit (find-symbol "ENTRY" package) '(1)))))
           "Configured macro operator saw rewritten method syntax")))

(defun combination-publication-tests ()
  ;; The combining operator is an ordinary owned helper. Its writes must be
  ;; dependencies of the effective method, just like writes in method bodies.
  (multiple-value-bind (unit package)
      (make-fixture
       :combination-publication
       "((defclass component () ())
          (defclass holder () ((component :initarg :component :accessor component)))
          (define-method-combination install :operator install-component)
          (defun install-component (holder component) (setf (component holder) component))
          (defgeneric install-value (holder component) (:method-combination install))
          (defmethod install-value install ((holder holder) component) holder)
          (defmethod install-value install ((holder t) component) component)
          (defun construct () (make-instance 'holder :component (make-instance 'component)))
          (defun new-component () (make-instance 'component))
          (defun read-component (holder) (component holder))
          (defun write-component (holder component) (install-value holder component)))"
       "(construct new-component read-component write-component)"
       "((construct ()) (new-component ()) (read-component (holder)) (write-component (holder component)))"
       "(component (setf component) install-value)")
    (flet ((entry (name) (find-symbol name package)))
      (let* ((root (funcall (snowgrave:unit-function unit (entry "CONSTRUCT"))))
             (initial (funcall (snowgrave:unit-function unit (entry "READ-COMPONENT")) root))
             (other (funcall (snowgrave:unit-function unit (entry "NEW-COMPONENT"))))
             (writer (snowgrave:bind-entry unit (entry "WRITE-COMPONENT") (list root other)))
             (restore (snowgrave:bind-entry unit (entry "WRITE-COMPONENT") (list root initial))))
        (setf (fdefinition (entry "INSTALL-COMPONENT"))
              (lambda (&rest arguments) (declare (ignore arguments)) (error "Original combining operator")))
        (closer-mop:set-funcallable-instance-function
         (fdefinition (entry "INSTALL-VALUE"))
         (lambda (&rest arguments) (declare (ignore arguments)) (error "Original generic")))
        (check (eq other (funcall writer)) "Custom composition retained its original operator")
        (funcall restore)
        (let ((reader (snowgrave:bind-entry unit (entry "READ-COMPONENT") (list root)
                                          :roles (fixture-read package "((holder component))"))))
          (check-signals (error) (funcall writer) "Custom composition mutation bypassed cold publication")
          (check (eq initial (funcall restore)) "Rebuilt custom composition rejected an allowed store")
          (check (eq initial (funcall reader)) "Custom composition damaged the reader's seal"))))))

(defun combination-rejection-tests ()
  (check-signals (snowgrave:snowgrave-error :method-combination)
    (make-fixture :long-combination-refusal
                  "((define-method-combination authored () ((primary ()))
                       `(call-method ,(first primary)))
                     (defun entry () nil))"
                  "(entry)" "((entry ()))" "()")
    "Long-form combination was admitted without a source producer"))

(defun method-combination-tests ()
  (short-combination-tests)
  (combination-macro-tests)
  (combination-publication-tests)
  (combination-rejection-tests))
