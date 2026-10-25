(defpackage #:snowgrave.tests
  (:use #:common-lisp)
  (:import-from #:snowgrave.host-tools
                #:host-gc #:host-bytes-consed #:host-process-command)
  (:export #:run-tests))

(in-package #:snowgrave.tests)

(defvar *checks* 0)
(defvar *fixture-sequence* 0)
(defvar *events* nil)
(defvar *macro-expansion-count* 0)

(defmacro snapshot-token ()
  (incf *macro-expansion-count*))

(defun note-event (event)
  (push event *events*)
  event)

(defun external-operation (value)
  (+ value 100))

(defun switch-external-operation (value)
  (setf (fdefinition 'external-operation) (lambda (argument) (+ argument 200)))
  value)

(defun check (truth description &rest arguments)
  (incf *checks*)
  (unless truth
    (error "Snowgrave check failed: ~?" description arguments)))

(defmacro check-signals ((type &optional features) form description &rest arguments)
  (let ((caught (gensym "CONDITION")) (expected (gensym "FEATURES")))
    `(let ((,caught (handler-case (progn ,form nil) (,type (condition) condition)))
           (,expected ,features))
       (check (and ,caught
                   ,(if features
                        `(member (snowgrave:error-feature ,caught)
                                 (if (listp ,expected) ,expected (list ,expected)))
                        t))
              "~? (expected ~S~@[ with feature ~S~], got ~S)"
              ,description (list ,@arguments) ',type ,expected ,caught))))

(defun fixture-read (package text)
  (let ((*package* package) (*read-eval* nil))
    (read-from-string text)))

(defun make-fixture (tag source entries domains generics &key (universe "()") external shadows)
  "Load the original CLOS program and close exactly those owned source forms."
  (let* ((number (incf *fixture-sequence*))
         (package (make-package (format nil "SNOWGRAVE.CORE.FIXTURE.~D" number) :use '("COMMON-LISP")))
         (forms (progn (shadow shadows package) (fixture-read package source)))
         (classes (loop for form in forms when (eq (first form) 'defclass) collect (second form))))
    (mapc #'eval forms)
    (values
     (snowgrave:close-source-unit
      (list :forms forms) :unit-name (list :core tag number)
      :closed-classes classes
      :universe (remove-duplicates (append classes (fixture-read package universe)))
      :closed-generics (fixture-read package generics)
      :entries (fixture-read package entries)
      :external-domains (fixture-read package domains)
      :external-operations external)
     package)))

(defun observed-call (function arguments)
  (let ((*events* nil))
    (let ((results (multiple-value-list (apply function arguments))))
      (list results (reverse *events*)))))

(defun compare-entry (unit package name arguments &optional expected &key (native-p t))
  (let* ((symbol (find-symbol name package))
         (open (if native-p (observed-call (fdefinition symbol) arguments)
                   (or expected (error "A host-independent oracle is required."))))
         (closed (observed-call (snowgrave:unit-function unit symbol) arguments)))
    (when expected
      (check (equal open expected) "~A open observation: ~S, expected ~S" name open expected))
    (check (equal open closed) "~A differs: open ~S, closed ~S" name open closed)
    closed))
