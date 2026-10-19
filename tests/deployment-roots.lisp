(defpackage #:snowgrave.deployment.fixture (:use #:cl))
(in-package #:snowgrave.tests)

(defvar *deployment-test-sequence* 0)
(defun deployment-forms (text)
  (let ((*package* (find-package :snowgrave.deployment.fixture))) (read-from-string text)))

(defun close-deployment (forms &key (policy :entries) classes generics domains imports external-operations external-argument-domains)
  (snowgrave:close-source-unit
   (list :forms forms) :unit-name (list :deployment-roots (incf *deployment-test-sequence*))
   :deployment-roots policy :closed-classes classes :closed-generics generics :universe classes
   :entries '(snowgrave.deployment.fixture::entry)
   :external-domains (list (list 'snowgrave.deployment.fixture::entry domains)) :native-bindings imports
   :external-operations external-operations :external-argument-domains external-argument-domains))

(defun deployment-refusal (forms feature &rest options)
  (let ((condition (handler-case (progn (apply #'close-deployment forms options) nil)
                     (snowgrave:snowgrave-error (condition) condition))))
    (check (typep condition 'snowgrave:snowgrave-error))
    (check (eq feature (snowgrave:error-feature condition)))
    condition))

(defun deployment-retained-p (unit name)
  (member (snowgrave::function-name-key name)
          (getf (getf (snowgrave:unit-metadata unit) :deployment) :retained-callables) :test #'equal))

(defun check-deployment-parity (unit forms expected)
  (dolist (form forms) (eval form))
  (check (equalp expected (multiple-value-list (funcall 'snowgrave.deployment.fixture::entry))))
  (check (equalp expected (multiple-value-list (funcall (snowgrave:unit-function unit 'snowgrave.deployment.fixture::entry))))))

(defun deployment-fresh-test (unit expected &optional native-data)
  ;; One source and one FASL installation, each in a new runtime-only process.
  (let* ((root (asdf:system-source-directory "snowgrave"))
         (cache (merge-pathnames "snowgrave-deployment-fresh/" (uiop:temporary-directory)))
         (identity (getf (snowgrave:unit-metadata unit) :identity)))
    (uiop:with-temporary-file (:pathname source :stream source-stream :type "lisp")
      (snowgrave:write-unit-source unit source-stream) (finish-output source-stream)
      (uiop:with-temporary-file (:pathname metadata :stream metadata-stream :type "metadata")
        (snowgrave:write-unit-metadata unit metadata-stream) (finish-output metadata-stream)
        (dolist (compiledp '(nil t))
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
                                (assert (not (find-package "SNOWGRAVE.DEPLOYMENT.FIXTURE")))
                                (let ((data (copy-seq ',native-data)))
                                  (flet ((install ()
                                           ,(if compiledp
                                                `(multiple-value-bind (artifact warnings failure)
                                                     (compile-file ,source :output-file ,fasl)
                                                   (declare (ignore warnings)) (assert (not failure)) (load artifact))
                                                `(load ,source))))
                                    ,(if native-data
                                         `(snowgrave:with-native-bindings (',identity (list (list :data data))) (install))
                                         '(install)))
                                  (let* ((metadata (with-open-file (stream ,metadata) (read stream)))
                                         (entry (first (getf metadata :entries)))
                                         (key (or (getf entry :bound-code-key) (getf entry :code-key)))
                                         (function (fdefinition (intern (second key) (first key)))))
                                    (assert (equalp ',expected (multiple-value-list (funcall function))))
                                    (assert (eq :entries (getf (getf metadata :deployment) :root-policy)))
                                    (let ((package (find-package "SNOWGRAVE.DEPLOYMENT.FIXTURE")))
                                      (assert (not (fboundp (find-symbol "COLD" package))))
                                      (assert (not (fboundp (find-symbol "VALIDATE" package))))
                                      (assert (not (find-class (find-symbol "NODE" package) nil)))))
                                  ,@(when native-data '((assert (equalp #(nil nil nil) data)))))
                                (assert (not (fboundp 'snowgrave.sbcl:close-source)))
                                (format t "Entry-rooted runtime artifact executed.~%")))
                       (write form :stream driver-stream :readably t) (terpri driver-stream))
                     (finish-output driver-stream)
                     (check (search "Entry-rooted runtime artifact executed."
                                    (uiop:run-program
                                     (list "sbcl" "--no-sysinit" "--no-userinit" "--script" (namestring driver))
                                     :output :string :error-output *error-output*))))
                (when (probe-file fasl) (delete-file fasl))))))))))

(defun deployment-cem-source-tests ()
  ;; Alpha-renaming and a misleading ambient fcell must not change the
  ;; source binding of an ordinary helper named by the actual MOP CEM.
  (dolist (policy '(:selected :entries))
    (dolist (helper '(cem-helper renamed-cem-helper))
      (let* ((name (intern (symbol-name helper) :snowgrave.deployment.fixture))
             (forms (deployment-forms
                     (format nil "((defun ~A (x) (error \"CEM helper ~~S\" x))
                       (define-method-combination source-ritual () ((primary () :required t))
                         `(progn (~A 1) (call-method ,(first primary))))
                       (defgeneric cem-run (x) (:method-combination source-ritual))
                       (defmethod cem-run ((x t)) 17) (defun entry () (cem-run 0)))"
                             helper helper))))
        (dolist (form forms) (eval form))
        (let ((native (handler-case (funcall 'snowgrave.deployment.fixture::entry)
                        (simple-error (condition)
                          (list (simple-condition-format-control condition)
                                (simple-condition-format-arguments condition))))))
          (check (equal native '("CEM helper ~S" (1))))
          (setf (fdefinition name) #'identity)
          (let ((unit (close-deployment forms :policy policy :generics '(snowgrave.deployment.fixture::cem-run))))
            (check (deployment-retained-p unit name))
            (check (equal native
                          (handler-case (funcall (snowgrave:unit-function unit 'snowgrave.deployment.fixture::entry))
                            (simple-error (condition)
                              (list (simple-condition-format-control condition)
                                    (simple-condition-format-arguments condition)))))))))))
  ;; The CEM factory also resolves cold authored helpers in the disposable
  ;; builder world. Its result may be constant code with no runtime edge.
  (dolist (policy '(:selected :entries))
    (dolist (helper '(cem-recipe renamed-cem-recipe))
      (let* ((name (intern (symbol-name helper) :snowgrave.deployment.fixture))
             (forms (deployment-forms
                     (format nil "((defun ~A () 17)
                       (define-method-combination factory-ritual () ((primary () :required t))
                         (declare (ignore primary)) (~A))
                       (defgeneric factory-run (x) (:method-combination factory-ritual))
                       (defmethod factory-run ((x t)) 99) (defun entry () (factory-run 0)))"
                             helper helper))))
        (dolist (form forms) (eval form))
        (check (= 17 (funcall 'snowgrave.deployment.fixture::entry)))
        (setf (fdefinition name) (lambda () 23))
        (let ((unit (close-deployment forms :policy policy :generics '(snowgrave.deployment.fixture::factory-run))))
          (check (= 17 (funcall (snowgrave:unit-function unit 'snowgrave.deployment.fixture::entry))))
          (check (not (deployment-retained-p unit name)))))))
  ;; An implicit short-combination operator is the authored function name,
  ;; while its registration/qualifier name belongs to the builder namespace.
  (dolist (policy '(:selected :entries))
    (let ((forms (deployment-forms
                  "((defun gather-values (&rest values) (cons :combined values))
                     (define-method-combination gather-values)
                     (defgeneric short-run (x) (:method-combination gather-values))
                     (defmethod short-run gather-values ((x t)) :method)
                     (defun entry () (short-run 0)))")))
      (dolist (form forms) (eval form))
      (check (equal '(:combined :method) (funcall 'snowgrave.deployment.fixture::entry)))
      (setf (fdefinition 'snowgrave.deployment.fixture::gather-values) #'list)
      (let ((unit (close-deployment forms :policy policy :generics '(snowgrave.deployment.fixture::short-run))))
        (check (equal '(:combined :method) (funcall (snowgrave:unit-function unit 'snowgrave.deployment.fixture::entry))))
        (check (deployment-retained-p unit 'snowgrave.deployment.fixture::gather-values)))))
  ;; Composer receipts preserve unclassified returned origin just as normal
  ;; function arguments do. A helper cannot turn imported objects into safe
  ;; closed-class observations by receiving a CALL-METHOD result.
  (dolist (policy '(:selected :entries))
    (let ((forms (deployment-forms
                  "((defclass marker () ()) (defun relay-value (x) x)
                     (define-method-combination opaque-ritual () ((primary () :required t))
                       `(relay-value (call-method ,(first primary))))
                     (defgeneric opaque-run (x) (:method-combination opaque-ritual))
                     (defmethod opaque-run ((x t)) (opaque-value))
                     (defun entry () (typep (opaque-run 0) 'marker)))")))
      (dolist (form forms) (eval form))
      (setf (fdefinition 'snowgrave.deployment.fixture::opaque-value)
            (lambda () (make-instance 'snowgrave.deployment.fixture::marker)))
      (check (funcall 'snowgrave.deployment.fixture::entry))
      (deployment-refusal forms :external-result-class-observation :policy policy
                          :classes '(snowgrave.deployment.fixture::marker)
                          :generics '(snowgrave.deployment.fixture::opaque-run)
                          :external-operations '(snowgrave.deployment.fixture::opaque-value))))
  ;; Specialized ordinary sequence emission still carries any declared
  ;; external argument contract; CEM helper deferral cannot skip that audit.
  (dolist (policy '(:selected :entries))
    (deployment-refusal
     (deployment-forms
      "((define-method-combination reverse-ritual () ((primary () :required t))
          (declare (ignore primary)) '(reverse '(1 2)))
         (defgeneric reverse-run (x) (:method-combination reverse-ritual))
         (defmethod reverse-run ((x t)) 17) (defun entry () (reverse-run 0)))")
     :external-argument-contract :policy policy :generics '(snowgrave.deployment.fixture::reverse-run)
     :external-operations '(reverse) :external-argument-domains '((reverse (vector)))))
  ;; CALL-METHOD is a typed producer, while the surrounding LET/FLET
  ;; establishes ordinary lexical source bindings using the same owners.
  (dolist (policy '(:selected :entries))
    (let* ((forms (deployment-forms
                   "((defun step-one (x) (error \"Wrong ambient helper ~S\" x))
                      (define-method-combination source-ritual () ((primary () :required t))
                        `(let ((value (call-method ,(first primary))))
                           (flet ((step-one (x) (+ x 5)))
                             (values (step-one value) :lexical))))
                      (defgeneric cem-run (x) (:method-combination source-ritual))
                      (defmethod cem-run ((x t)) 17) (defun entry () (cem-run 0)))"))
           (unit (close-deployment forms :policy policy :generics '(snowgrave.deployment.fixture::cem-run))))
      (check-deployment-parity unit forms '(22 :lexical))
      (check (not (deployment-retained-p unit 'snowgrave.deployment.fixture::step-one)))))
  t)

(defun deployment-root-tests ()
  (deployment-cem-source-tests)
  ;; Default policy retains the original reflection restriction and roots.
  (let ((forms (deployment-forms "((defun cold (x) (class-of x)) (defun entry () 17))")))
    (deployment-refusal forms 'class-of :policy :selected)
    (let ((unit (close-deployment forms)))
      (check-deployment-parity unit forms '(17))
      (check (not (deployment-retained-p unit 'snowgrave.deployment.fixture::cold)))
      (check (= 2 (length (getf (getf (snowgrave:unit-metadata unit) :deployment) :sealed-source))))
      (signals error (snowgrave:unit-function unit 'snowgrave.deployment.fixture::cold))))
  (dolist (bad '(nil :cold :all (:entry)))
    (deployment-refusal (deployment-forms "((defun entry () 17))") :deployment-roots :policy bad))
  (let* ((forms (deployment-forms
                 "((defclass node () ())
                    (defun cold (x name)
                      (list (class-of x) (find-class 'node nil) (find-class name nil)
                            (change-class x 'node)
                            (slot-missing (find-class 'node) x 'missing 'slot-value)
                            (slot-unbound (find-class 'node) x 'missing)))
                    (defun entry () 17))"))
         (unit (close-deployment forms :classes '(snowgrave.deployment.fixture::node))))
    (check-deployment-parity unit forms '(17))
    (check (not (deployment-retained-p unit 'snowgrave.deployment.fixture::cold))))
  ;; Every real edge retains the cold helper; names and apparent cold intent
  ;; do not waive closed CLASS-OF or a function's arbitrary future callers.
  (dolist (tail '("(defun entry () (cold 1))"
                  "(defun relay () (cold 1)) (defun entry () (relay))"
                  "(defun entry () #'cold)"
                  "(defparameter *saved* #'cold) (defun entry () 17)"
                  "(defun entry () (funcall (if t #'cold #'identity) 1))"))
    (deployment-refusal (deployment-forms (format nil "((defun cold (x) (class-of x)) ~A)" tail)) 'class-of))
  ;; Syntax and load-time execution admission still inspect all source.
  (deployment-refusal (deployment-forms "((defun cold () (load-time-value (get-universal-time))) (defun entry () 17))") :load-time-capture)
  (deployment-refusal (deployment-forms "((defun cold (x) (cond (t . :bad))) (defun entry () 17))") :conditional-clause)
  (deployment-refusal (deployment-forms "((defun cold (class) (make-instance class)) (defun entry () (cold 'symbol)))") :dynamic-construction-class)
  ;; A reached ordinary helper remains one definition despite recursion.
  (let* ((forms (deployment-forms "((defun cold (x) (class-of x))
                                    (defun walk (n) (if (zerop n) 17 (walk (1- n))))
                                    (defun entry () (walk 3)))"))
         (unit (close-deployment forms)))
    (check-deployment-parity unit forms '(17))
    (check (deployment-retained-p unit 'snowgrave.deployment.fixture::walk))
    (check (= 1 (count (snowgrave::function-name-key 'snowgrave.deployment.fixture::walk)
                       (getf (snowgrave:unit-metadata unit) :definitions)
                       :key (lambda (row) (third (getf row :definition-key))) :test #'equal))))
  ;; Sealing an unentered GF does not publish it. Reaching it by any real
  ;; invocation/capture retains its entire conservative cell partition.
  (dolist (tail '("(defun entry () (validate (make-instance 'node)))"
                  "(defun entry () #'validate)"
                  "(defparameter *saved* #'validate) (defun entry () 17)"))
    (deployment-refusal
     (deployment-forms (format nil "((defclass node () ()) (defun cold (x) (class-of x))
                                     (defgeneric validate (x)) (defmethod validate ((x node)) (cold x)) ~A)" tail))
     'class-of :classes '(snowgrave.deployment.fixture::node) :generics '(snowgrave.deployment.fixture::validate)))
  ;; Runtime construction pulls defaults, selected INIT/SHARED and their
  ;; complete next-method chain back into the same dependency fixed point.
  (dolist (source '("((defclass node () ((payload :initform (cold 1)))) (defun cold (x) (class-of x)) (defun entry () (make-instance 'node) 17))"
                    "((defclass node () ((payload :initarg :payload)) (:default-initargs :payload (cold 1))) (defun cold (x) (class-of x)) (defun entry () (make-instance 'node) 17))"
                    "((defclass node () ()) (defun cold (x) (class-of x))
                       (defmethod initialize-instance :after ((x node) &key) (cold x)) (defun entry () (make-instance 'node) 17))"))
    (deployment-refusal (deployment-forms source) 'class-of :classes '(snowgrave.deployment.fixture::node)
                        :generics (when (search "defmethod" source :test #'char-equal) '(initialize-instance shared-initialize))))
  (let* ((forms (deployment-forms
                 "((defclass node () ((payload :initform (default-value))))
                    (defun default-value () 17) (defun cold (x) (class-of x))
                    (defgeneric validate (x)) (defmethod validate ((x node)) (cold x))
                    (defparameter *events* nil) (defgeneric run (x))
                    (defmethod run :around ((x node)) (push :around-before *events*)
                      (multiple-value-prog1 (call-next-method) (push :around-after *events*)))
                    (defmethod run :before ((x node)) (push :before *events*))
                    (defmethod run ((x node)) (push :primary *events*) (values (slot-value x 'payload) :done))
                    (defmethod run :after ((x node)) (push :after *events*))
                    (defun entry () (let ((*events* nil))
                      (multiple-value-bind (a b) (unwind-protect (run (make-instance 'node)) (push :cleanup *events*))
                        (values a b (reverse *events*))))))"))
         (unit (close-deployment forms :classes '(snowgrave.deployment.fixture::node)
                                 :generics '(snowgrave.deployment.fixture::run snowgrave.deployment.fixture::validate)))
         (expected '(17 :done (:around-before :before :primary :after :around-after :cleanup))))
    (check-deployment-parity unit forms expected)
    (check (deployment-retained-p unit 'snowgrave.deployment.fixture::run))
    (check (deployment-retained-p unit 'snowgrave.deployment.fixture::default-value))
    (check (not (deployment-retained-p unit 'snowgrave.deployment.fixture::validate)))
    (check (= 1 (length (getf (snowgrave:unit-metadata unit) :dispatch))))
    (deployment-fresh-test unit expected))
  ;; Generated initialization delegation is not an authored source call,
  ;; but both protocol generics and the actual AFTER method remain deployed.
  (let* ((forms (deployment-forms
                 "((defclass node () ((payload :initform 17))) (defparameter *events* nil)
                    (defun cold (x) (class-of x)) (defgeneric validate (x))
                    (defmethod validate ((x node)) (cold x))
                    (defmethod initialize-instance :after ((x node) &key) (push :initialized *events*))
                    (defun entry () (let ((*events* nil))
                      (let ((x (make-instance 'node))) (values (slot-value x 'payload) *events*)))))"))
         (unit (close-deployment forms :classes '(snowgrave.deployment.fixture::node)
                                 :generics '(initialize-instance shared-initialize snowgrave.deployment.fixture::validate))))
    (check-deployment-parity unit forms '(17 (:initialized)))
    (check (deployment-retained-p unit 'initialize-instance))
    (check (deployment-retained-p unit 'shared-initialize))
    (check (not (deployment-retained-p unit 'snowgrave.deployment.fixture::validate))))
  (let* ((forms (deployment-forms
                 "((defgeneric run (x)) (defmethod run ((x t)) x) (defun entry () #'run))"))
         (unit (close-deployment forms :generics '(snowgrave.deployment.fixture::run)))
         (captured (funcall (snowgrave:unit-function unit 'snowgrave.deployment.fixture::entry))))
    (check (deployment-retained-p unit 'snowgrave.deployment.fixture::run))
    (check (= 23 (funcall captured 23))))
  ;; An ambient registered combination is not source provenance, even when
  ;; the generic would be omitted from runtime deployment.
  (eval (deployment-forms "(define-method-combination untracked-combination () ((primary () :required t)) `(call-method ,(first primary)))"))
  (deployment-refusal
   (deployment-forms "((defgeneric validate (x) (:method-combination untracked-combination)) (defun entry () 17))")
   :method-combination-provenance :generics '(snowgrave.deployment.fixture::validate))
  ;; A custom CEM is part of the same retained dependency graph, not just
  ;; its most-specific authored method. Cold calls in its expansion count.
  (dolist (calledp '(nil t))
    (let* ((forms (deployment-forms
                   (format nil "((defun cold (x) (class-of x))
                     (define-method-combination ritual () ((primary () :required t))
                       `(progn (cold 1) (call-method ,(first primary))))
                     (defgeneric run (x) (:method-combination ritual))
                     (defmethod run ((x t)) 17) (defun entry () ~A))"
                           (if calledp "(run 0)" "17")))))
      (if calledp
          (deployment-refusal forms 'class-of :generics '(snowgrave.deployment.fixture::run))
          (let ((unit (close-deployment forms :generics '(snowgrave.deployment.fixture::run))))
            (check-deployment-parity unit forms '(17))
            (check (not (deployment-retained-p unit 'snowgrave.deployment.fixture::run)))))))
  (let* ((forms (deployment-forms
                 "((defun cold (x) (class-of x))
                    (define-method-combination ritual () ((primary () :required t)) `(call-method ,(first primary)))
                    (defgeneric run (x) (:method-combination ritual))
                    (defmethod run ((x t)) (values 17 :tag)) (defun entry () (run 0)))"))
         (unit (close-deployment forms :generics '(snowgrave.deployment.fixture::run))))
    (check-deployment-parity unit forms '(17 :tag))
    (check (deployment-retained-p unit 'snowgrave.deployment.fixture::run)))
  ;; A retained GF's non-entered class cell remains audited in this profile.
  (deployment-refusal
   (deployment-forms "((defclass node () ()) (defclass other () ()) (defgeneric run (x))
                       (defmethod run ((x node)) 17) (defmethod run ((x other)) (class-of x))
                       (defun entry () (run (make-instance 'node))))")
   'class-of :classes '(snowgrave.deployment.fixture::node snowgrave.deployment.fixture::other)
   :generics '(snowgrave.deployment.fixture::run))
  ;; Fixed-root configuration keeps all existing graph/native/custody proofs,
  ;; while an unentered validation method cannot become a supervisor root.
  (let* ((forms (deployment-forms
                 "((defclass node () ((data :initarg :data :reader data)))
                    (defun cold (x) (class-of x)) (defgeneric validate (x))
                    (defmethod validate ((x node)) (cold x))
                    (defun entry (root) (length (fill (data root) nil))))")))
    (dolist (form forms) (eval form))
    (let* ((data (vector 1 2 3))
           (root (make-instance 'snowgrave.deployment.fixture::node :data data))
           (unit (close-deployment forms :classes '(snowgrave.deployment.fixture::node)
                                        :generics '(snowgrave.deployment.fixture::data snowgrave.deployment.fixture::validate)
                                        :domains (list (list 'eql root)) :imports (list (list :data data)))))
      (signals error (snowgrave:unit-function unit 'snowgrave.deployment.fixture::entry))
      (signals error (snowgrave:unit-function unit 'snowgrave.deployment.fixture::validate :bind-configuration t))
      (check (= 3 (funcall (snowgrave:unit-function unit 'snowgrave.deployment.fixture::entry :bind-configuration t))))
      (check (equalp #(nil nil nil) data))
      (check (not (deployment-retained-p unit 'snowgrave.deployment.fixture::validate)))
      (deployment-fresh-test unit '(3) #(1 2 3))))
  ;; Statically short calls must not lose a GF because no normal argument
  ;; shape exists. Its emitted host minimum-arity path still owns the error.
  (let* ((forms (deployment-forms "((defgeneric run (x)) (defmethod run ((x t)) 17) (defun entry () (run)))"))
         (unit (close-deployment forms :generics '(snowgrave.deployment.fixture::run))))
    (check (deployment-retained-p unit 'snowgrave.deployment.fixture::run))
    (signals program-error (funcall (snowgrave:unit-function unit 'snowgrave.deployment.fixture::entry)))))
