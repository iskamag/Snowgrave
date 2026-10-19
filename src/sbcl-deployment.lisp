(in-package #:snowgrave.sbcl)

(defun entry-rooted-deployment-p (build)
  (eq (getf (build-declaration build) :deployment-roots) :entries))

(defun deployed-generics (build)
  ;; The declaration seals the complete authored world. In entry-rooted mode,
  ;; table presence records an actual call/capture dependency, even when its
  ;; normal argument-shape set is empty (for example, a short-arity call).
  (remove-if-not
   (lambda (name)
     (or (not (entry-rooted-deployment-p build))
         (and (build-generic-call-shapes build)
              (nth-value 1 (gethash name (build-generic-call-shapes build))))))
   (getf (build-declaration build) :closed-generics)))

(defun retain-construction-initialization (build)
  ;; Generated stock delegation is a real dependency, not an authored call
  ;; node in TRANSFORM-FORM. Reuse the capture owner conservatively: all
  ;; selected initialization cells remain audited, including custom methods.
  (when (entry-rooted-deployment-p build)
    (dolist (name '(initialize-instance shared-initialize))
      (when (member-name name (getf (build-declaration build) :closed-generics))
        (audit-generic-call-shape build name nil t nil)))))

(defun open-class-name-expression (build expression package local)
  ;; FIND-CLASS and CHANGE-CLASS accept symbolic designators. Preserve their
  ;; evaluation point and map only sealed source names into the disposable
  ;; world. Built-ins, foreign names and actual class objects keep host meaning.
  (let ((value (gensym "OPEN-CLASS-NAME-")))
    `(let ((,value ,(transform-form build expression package :open t :local local)))
       (cond ,@(mapcar (lambda (name)
                         `((eq ,value ',name) ',(mapped-name name package)))
                       (build-classes build))
             (t ,value)))))

(defun open-reflection-form (build form package local)
  ;; This code is compiled only in the disposable open world. Every reached
  ;; closed occurrence still goes through TRANSFORM-FORM's rejection branch.
  ;; No host metaobject, callable or operation is added to the deployed ABI.
  `(,(first form)
    ,@(loop for argument in (rest form) for position from 0
            collect (if (or (and (eq (first form) 'find-class) (= position 0))
                            (and (eq (first form) 'change-class) (= position 1)))
                        (open-class-name-expression build argument package local)
                        (transform-form build argument package :open t :local local)))))

(defun validate-generic-protocol (build generic gf)
  ;; One protocol owner for both source-universe admission and emitted code.
  (if (initialization-generic-p generic)
      (unless (and (eq (class-of gf) (find-class 'standard-generic-function))
                   (typep (sb-mop:generic-function-method-combination gf) 'sb-pcl::standard-method-combination))
        (fail build 'snowgrave:unclosed-class-operation :initialization-generic-protocol
              "Initialization generic classes and combinations require exact host normalization." :materialization))
      (progn
        (unless (eq (class-of gf) (find-class 'standard-generic-function))
          (fail build 'snowgrave:unsupported-definition :generic-function-class
                "Custom generic-function classes need an exact argument/applicability/error contract." :materialization))
        (unless (or (typep (sb-mop:generic-function-method-combination gf) 'sb-pcl::standard-method-combination)
                    (let ((name (source-generic-combination build generic)))
                      (or (authored-combination-name build name) (member name *host-method-combinations*))))
          (fail build 'snowgrave:unsupported-definition :custom-method-combination
                "Custom combinations need their own audited normalized source extension." :materialization)))))

(defun audit-sealed-generic-provenance (build)
  ;; Omitting runtime code does not omit source/MOP provenance. Inspect actual
  ;; methods without transforming their bodies or invoking custom CEM code.
  (dolist (name (getf (build-declaration build) :closed-generics))
    (let ((gf (open-generic build name)))
      (validate-generic-protocol build name gf)
      (if (initialization-generic-p name)
          (dolist (layout (build-layouts build))
            (initialization-methods build name
                                    (find-class (mapped-name (getf layout :class) (build-open-package build)))))
          (dolist (method (sb-mop:generic-function-methods gf))
            (unless (authored-method build name method)
              (fail build 'snowgrave:unsupported-definition :method-provenance
                    "A sealed generic method lacks authored or accessor provenance." :materialization)))))))

(defun deployment-evidence (build)
  (let* ((generics (deployed-generics build))
         (functions (remove-if-not
                     (lambda (name) (nth-value 1 (gethash name (build-function-domains build))))
                     (build-functions build)))
         (retained (append functions generics)))
    (list :root-policy (or (getf (build-declaration build) :deployment-roots) :selected)
          :public-entries (mapcar #'snowgrave::function-name-key
                                  (getf (build-declaration build) :entries))
          :sealed-source
          (mapcar (lambda (definition)
                    (list :source-key (list (build-identity build) (snowgrave:authored-definition-position definition))
                          :kind (snowgrave:authored-definition-kind definition)
                          :name-key (snowgrave::function-name-key (snowgrave:authored-definition-name definition))))
                  (snowgrave:authored-source-definitions (build-source build)))
          :sealed-classes (mapcar #'snowgrave::function-name-key (build-classes build))
          :sealed-generics (mapcar #'snowgrave::function-name-key
                                  (getf (build-declaration build) :closed-generics))
          :retained-callables (mapcar #'snowgrave::function-name-key retained)
          :omitted-callables
          (loop for name in (append (build-functions build) (getf (build-declaration build) :closed-generics))
                unless (member-name name retained)
                  collect (list :name-key (snowgrave::function-name-key name)
                                :reason :unreachable-from-deployment-roots))
          :proof :shared-call-capture-and-construction-fixed-point
          :cell-coverage :whole-sealed-partition-of-each-retained-generic)))

;;;; Implicit callable authority in native generic errors.

(defun generic-error-private-classes (build domain)
  ;; A captured node or freshly constructed record has one exact layout.
  ;; An initializing receiver carries identity/state, but its class fact can
  ;; still be nominal (a base-specialized method also accepts subclasses).
  (cond ((relational-value-domain-p domain)
         (generic-error-private-classes build (third domain)))
        ((graph-node-domain-p domain) (list (third domain)))
        ((owned-record-domain-p domain) (list (second domain)))
        ((or (initializing-record-domain-p domain)
             (member-name domain (build-classes build)))
         (let ((base (if (initializing-record-domain-p domain) (third domain) domain)))
           (remove-if-not (lambda (class) (subtype-domain-p build class base))
                          (build-classes build))))))

(defun generic-error-axis-possible-p (build domain cell axis)
  ;; Reflect the ordered emitted CELL-TEST guards, not only method
  ;; specialization overlap. Private guards test an exact layout; native
  ;; guards test TYPEP. UNKNOWN remains conservative.
  (some
   (lambda (part)
     (let ((classes (generic-error-private-classes build part)))
       (if classes
           (some (lambda (class)
                   (name= cell
                          (find-if
                           (lambda (guard)
                             (if (member-name guard (build-classes build))
                                 (name= class guard)
                                 (subtype-domain-p build class guard))) axis)))
                 classes)
           (and (nth-value 1 (intersect-method-cell-domain build part cell))
                (not (loop for earlier in axis until (name= earlier cell)
                           thereis (and (not (member-name earlier (build-classes build)))
                                        (subtype-domain-p build part earlier))))))))
   (domain-alternatives domain)))

(defun generic-miss-has-program-caller-p (build generic)
  ;; Capture rows are retained arbitrary-body obligations, not evidence that
  ;; this error executes. Keep raw actual tuples: projected method bindings
  ;; have already forgotten arity and dispatch alternatives.
  (let ((shapes (gethash generic (build-generic-call-shapes build))))
    (when shapes
      (loop for key being the hash-keys of shapes using (hash-value input)
            thereis
            (destructuring-bind (capture variable-tail count literal-names) key
              (declare (ignore literal-names))
              (and (not capture)
                   (or variable-tail (>= count (length *cell-domains*)))
                   (or (null *cell-axis-domains*)
                       (let ((domains (if (record-flow-input-p input)
                                          (record-flow-positional-inputs input) input)))
                         (loop for cell in *cell-domains* for axis in *cell-axis-domains*
                               for position from 0
                               always (generic-error-axis-possible-p
                                       build (if (< position count) (nth position domains) :unknown)
                                       cell axis))))))))))

(defun audit-generic-minimum-arity (build generic required count capture)
  (when (and (graph-state-profile-p build) (not *collect-function-flow*)
             (not capture) (< count required))
    ;; An unknown APPLY tail may be empty. A statically expanded complete
    ;; tuple has already passed through the shared call/lambda binder.
    (fail build 'snowgrave:unclosed-call :graph-state-generic-authority
          (format nil "A possible short call to ~S exposes its relocated generic in the native arity condition."
                  generic) :reachability)))

(defun audit-standard-generic-authority (build generic)
  (when (and (graph-state-profile-p build) (not *collect-function-flow*)
             (or (initialization-generic-p generic)
                 (generic-miss-has-program-caller-p build generic)))
    ;; Native miss conditions and their retry restart retain the generic.
    ;; Unknown-input body auditing does not establish an external result or
    ;; effect ABI for that callable. Initialization root phases include
    ;; retention placeholders, so they cannot discharge this obligation.
    (fail build 'snowgrave:unclosed-call :graph-state-generic-authority
          (format nil "A possible standard miss of ~S exposes relocated callable authority without a public calling contract."
                  generic) :reachability)))
