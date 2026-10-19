(defpackage #:snowgrave.cold-source.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass #:defgeneric #:defmethod))
(in-package #:snowgrave.tests)

(defvar *cold-source-unit-sequence* 0)
(defun snowgrave.cold-source.fixture::host-token () 17)

(defun cold-source-forms (text)
  (let ((*package* (find-package :snowgrave.cold-source.fixture)))
    (read-from-string text)))

(defun close-cold-source (forms tag &key classes generics externals)
  (snowgrave:close-source-unit
   (list :forms forms)
   :unit-name (list :cold-source-boundary tag (incf *cold-source-unit-sequence*))
   :closed-classes classes :closed-generics generics :universe classes
   :entries '(snowgrave.cold-source.fixture::entry)
   :external-domains '((snowgrave.cold-source.fixture::entry nil))
   :external-operations externals))

(defun cold-source-definition-p (unit name)
  (find (snowgrave::function-name-key name) (getf (snowgrave:unit-metadata unit) :definitions)
        :key (lambda (row) (third (getf row :definition-key))) :test #'equal))

(defun check-cold-source-values (unit forms expected)
  (dolist (form forms) (eval form))
  (let ((native (multiple-value-list (funcall 'snowgrave.cold-source.fixture::entry))))
    (check (equal expected native))
    (check (equal native
                  (multiple-value-list
                   (funcall (snowgrave:unit-function unit 'snowgrave.cold-source.fixture::entry)))))))

(defun check-cold-source-refusal (forms tag feature position &key classes generics)
  (let ((condition (handler-case
                       (progn (close-cold-source forms tag :classes classes :generics generics) nil)
                     (snowgrave:snowgrave-error (condition) condition))))
    (check (typep condition 'snowgrave:snowgrave-error))
    (check (eq feature (snowgrave:error-feature condition)))
    (check (= position (second (snowgrave:error-source-key condition))))))

(defun cold-source-fresh-test (unit)
  ;; Temporary files keep this runtime-only replay independent of the builder
  ;; and of the source checkout's build directory.
  (let* ((root (asdf:system-source-directory "snowgrave"))
         (cache (merge-pathnames "snowgrave-cold-source-fresh/" (uiop:temporary-directory))))
    (uiop:with-temporary-file (:pathname source :stream source-stream :type "lisp")
      (snowgrave:write-unit-source unit source-stream)
      (finish-output source-stream)
      (uiop:with-temporary-file (:pathname metadata :stream metadata-stream :type "metadata")
        (snowgrave:write-unit-metadata unit metadata-stream)
        (finish-output metadata-stream)
        (uiop:with-temporary-file (:pathname driver :stream driver-stream :type "lisp")
          (let ((fasl (make-pathname :type "fasl" :defaults source)))
            (unwind-protect
                 (progn
                   (dolist (form
                            `((require :asdf)
                              (make-package "SNOWGRAVE.TESTS" :use '("COMMON-LISP"))
                              (asdf:initialize-source-registry
                               '(:source-registry (:directory ,root) :ignore-inherited-configuration))
                              (asdf:initialize-output-translations
                               '(:output-translations (t ,cache) :ignore-inherited-configuration))
                              (asdf:load-system "snowgrave")
                              (load ,(merge-pathnames "scripts/artifact-functions.lisp" root))
                              (assert (not (find-package "SNOWGRAVE.COLD-SOURCE.FIXTURE")))
                              (multiple-value-bind (artifact warnings failure)
                                  (compile-file ,source :output-file ,fasl)
                                (declare (ignore warnings)) (assert (not failure)) (load artifact))
                              (let* ((metadata (with-open-file (stream ,metadata) (read stream)))
                                     (package (find-package "SNOWGRAVE.COLD-SOURCE.FIXTURE")))
                                (dolist (name '("COLD" "ENTRY"))
                                  (assert (not (fboundp (find-symbol name package)))))
                                (assert (not (find-class (find-symbol "NODE" package) nil)))
                                (assert (= 7 (funcall
                                              (uiop:symbol-call :snowgrave.artifact-tests :artifact-function
                                                                metadata "ENTRY"))))
                                (assert (= 17 (funcall
                                               (uiop:symbol-call :snowgrave.artifact-tests :artifact-function
                                                                 metadata "COLD")))))
                              (assert (not (fboundp 'snowgrave.sbcl:close-source)))
                              (format t "Fresh cold-source boundary executed.~%")))
                     (write form :stream driver-stream :readably t) (terpri driver-stream))
                   (finish-output driver-stream)
                   (check (search "Fresh cold-source boundary executed."
                                  (uiop:run-program
                                   (list "sbcl" "--no-sysinit" "--no-userinit" "--script" (namestring driver))
                                   :output :string :error-output *error-output*))))
              (when (probe-file fasl) (delete-file fasl)))))))))

(defun cold-source-boundary-tests ()
  (let ((*package* (find-package :snowgrave.cold-source.fixture)))
    ;; An ordinary unused body compiles in the disposable host world. Its
    ;; call/capture targets must neither be deployed nor contaminate the
    ;; closed dependency report. Macro normalization still sees all source.
    (dolist (spec '((:assert "(assert (plusp x))" sb-kernel:assert-error)
                    (:host-call "(get-universal-time)" get-universal-time)
                    (:host-capture "#'get-universal-time" get-universal-time)
                    (:ordinary-capture "#'fill" fill)))
      (let* ((forms (cold-source-forms
                     (format nil "((defun cold (x) (declare (ignorable x)) ~A) (defun entry () 7))"
                             (second spec))))
             (unit (close-cold-source forms (first spec)))
             (dependencies (getf (snowgrave:unit-report unit) :dependencies)))
        (check-cold-source-values unit forms '(7))
        (check (not (cold-source-definition-p unit (intern "COLD"))))
        (check (not (member (snowgrave::function-name-key (third spec))
                            dependencies :test #'equal)))
        (check (not (find (snowgrave::function-name-key (intern "COLD"))
                          (getf (getf (snowgrave:unit-report unit) :ordinary-function-flow) :functions)
                          :key (lambda (row) (getf row :function-key)) :test #'equal)))))
    ;; Open calls to an authored helper must likewise be absent from the
    ;; deployed dependency report when their complete chain is unused.
    (let* ((forms (cold-source-forms
                   "((defun cold-leaf () 17) (defun cold () (cold-leaf)) (defun entry () 7))"))
           (unit (close-cold-source forms :unused-helper-chain)))
      (check-cold-source-values unit forms '(7))
      (dolist (name '("COLD" "COLD-LEAF"))
        (check (not (cold-source-definition-p unit (intern name))))
        (check (not (member (snowgrave::function-name-key (intern name))
                            (getf (snowgrave:unit-report unit) :dependencies) :test #'equal)))))
    ;; Once a helper is reached, the same undeclared host targets still fail
    ;; the closed call/capture audit, attributed to the helper's own source.
    (dolist (spec '((:reached-assert "(assert (plusp x)) x")
                    (:reached-host-call "(get-universal-time)")
                    (:reached-host-capture "#'get-universal-time")))
      (check-cold-source-refusal
       (cold-source-forms
        (format nil "((defun cold (x) (declare (ignorable x)) ~A) (defun entry () (cold 1)))" (second spec)))
       (first spec) :call-target 1))
    ;; Keep full-source execution/reproducibility restrictions: the compiler
    ;; may execute LTV inside a function whose runtime body is never called.
    (check-cold-source-refusal
     (cold-source-forms "((defun cold () (load-time-value (get-universal-time))) (defun entry () 7))")
     :unused-load-time-execution :load-time-capture 1)
    (check-cold-source-refusal
     (cold-source-forms "((defun cold () 17) (defparameter *saved* (cold)) (defun entry () 7))")
     :unadmitted-global-call :global-initializer 2)
    (check-cold-source-refusal
     (cold-source-forms "((defun cold (x) (class-of x)) (defun entry () 7))")
     :unchanged-reflection-fragment 'class-of 1)
    ;; Published globals independently retain captures. Even ENTRY=7 cannot
    ;; prune a helper whose callable is installed into the source global.
    (let* ((forms (cold-source-forms
                   "((defun cold () 17) (defparameter *saved* #'cold) (defun entry () 7))"))
           (unit (close-cold-source forms :global-capture-root)))
      (check-cold-source-values unit forms '(7))
      (check (cold-source-definition-p unit (intern "COLD")))
      (check (= 17 (funcall (test-code-function unit (intern "COLD"))))))
    (check-cold-source-refusal
     (cold-source-forms
      "((defun cold () (get-universal-time)) (defparameter *saved* #'cold) (defun entry () 7))")
     :global-capture-undeclared-target :call-target 1)
    ;; This admitted initializer fails at the existing callable-ABI boundary;
    ;; inference must blame the global, not the following ENTRY definition.
    (check-cold-source-refusal
     (cold-source-forms "((defparameter *saved* #'fill) (defun entry () 7))")
     :global-capture-source-key :ordinary-function-capture 1)
    ;; Selected method and compiler-generated initialization are independent
    ;; roots, even without a direct call from ENTRY to their helper.
    (check-cold-source-refusal
     (cold-source-forms
      "((defclass node () ()) (defgeneric visit (x))
         (defmethod visit ((x node)) (declare (ignore x)) (get-universal-time)) (defun entry () 7))")
     :selected-method-root :call-target 3 :classes (list (intern "NODE")) :generics (list (intern "VISIT")))
    (dolist (initializer '("((payload :initform #'cold))"
                           "((payload :initarg :payload)) (:default-initargs :payload #'cold)"))
      (let* ((forms (cold-source-forms
                     (format nil "((defun cold () 17) (defclass node () ~A)
                                   (defun entry () (make-instance 'node) 7))" initializer)))
             (unit (close-cold-source forms (list :constructor-capture initializer)
                                      :classes (list (intern "NODE")))))
        (check-cold-source-values unit forms '(7))
        (check (cold-source-definition-p unit (intern "COLD")))
        (check (= 17 (funcall (test-code-function unit (intern "COLD")))))
        (when (search "default-initargs" initializer) (cold-source-fresh-test unit)))
      (check-cold-source-refusal
       (cold-source-forms
        (format nil "((defun cold () (get-universal-time)) (defclass node () ~A)
                      (defun entry () (make-instance 'node) 7))" initializer))
       (list :constructor-capture-undeclared-target initializer) :call-target 1 :classes (list (intern "NODE"))))
    ;; A direct initializer keeps its defining class's source key. Inherited
    ;; initializers belong to the ancestor, not the constructed subclass or
    ;; ENTRY that happens to trigger materialization.
    (dolist (initializer '("((payload :initform (get-universal-time)))"
                           "((payload :initarg :payload)) (:default-initargs :payload (get-universal-time))"))
      (dolist (inheritedp '(nil t))
        (let* ((owner (if inheritedp "ancestor" "node"))
               (forms (cold-source-forms
                       (format nil "((defclass ~A () ~A) ~A (defun entry () (make-instance 'node) 7))"
                               owner initializer (if inheritedp "(defclass node (ancestor) ())" "")))))
          (check-cold-source-refusal
           forms (list :direct-initializer-owner initializer inheritedp) :call-target 1
           :classes (if inheritedp (list (intern "ANCESTOR") (intern "NODE")) (list (intern "NODE")))))))
    ;; The host may share constant initfunctions across ancestors. Distinct
    ;; owner wrappers must not reject the same EQ scalar/literal expression.
    (let* ((forms (cold-source-forms
                   "((defclass ancestor ()
                        ((payload :initarg :payload :initform 17) (empty :initarg :empty :initform nil))
                        (:default-initargs :payload 17 :empty nil))
                     (defclass node (ancestor) ((payload :initform 17) (empty :initform nil))
                        (:default-initargs :payload 17 :empty nil))
                     (defun entry () (let ((object (make-instance 'node)))
                                       (values (slot-value object 'payload) (slot-value object 'empty)))))"))
           (unit (close-cold-source forms :shared-constant-initializer-owners
                                    :classes (list (intern "ANCESTOR") (intern "NODE")))))
      (check-cold-source-values unit forms '(17 nil)))
    ;; Capturing an authored function inside LTV uses the null lexical
    ;; environment, while ordinary FUNCTION/direct local calls keep FLET.
    (let* ((forms (cold-source-forms
                   "((defun cold () 17)
                     (defun entry () (flet ((cold () 23))
                                       (values (cold) (funcall #'cold) (funcall (load-time-value #'cold))))))"))
           (unit (close-cold-source forms :authored-and-lexical-identity)))
      (check-cold-source-values unit forms '(23 23 17)))
    ;; A declared external remains the exact host callable in both captures.
    (let* ((forms (cold-source-forms
                   "((defun entry () (values #'host-token (load-time-value #'host-token))))"))
           (unit (close-cold-source forms :external-identity :externals (list (intern "HOST-TOKEN")))))
      (check-cold-source-values unit forms
                                (list (fdefinition (intern "HOST-TOKEN")) (fdefinition (intern "HOST-TOKEN")))))
    t))
