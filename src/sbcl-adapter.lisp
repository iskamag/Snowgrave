(eval-when (:compile-toplevel :load-toplevel :execute) (require :sb-introspect) (require :sb-cltl2))
(in-package #:snowgrave.sbcl)

;; This adapter admits a deliberately explicit source fragment. The proof of
;; freshness is constructive: all bodies are read again, checked, and emitted
;; into a fresh package, and the emitted forms contain no builder constants.
;; It never installs a CLOS object in an authored function cell. Initialization
;; protocol methods temporarily specialize only disposable builder classes.

(defvar *published-identities* (make-hash-table :test #'equal))
(defvar *builder-counter* 0)
(defvar *argument-domains* nil)
(defvar *cell-domains* nil)
(defvar *cell-axis-domains* nil)
(defvar *function-bindings* nil)
(defvar *generated-class-operation* nil)
(defvar *current-method* nil)
(defvar *active-construction-classes* nil)
(defvar *initialization-phase* nil)
(defvar *initialization-next* nil)
(defvar *initialization-plan* nil)
(defvar *flow-value-receipts* nil)
(defvar *flow-input-row* nil)
(defvar *flow-unknown-effect* nil)
(defvar *flow-deferred-call-p* nil)
(defvar *flow-exit-receipts* nil)
(defvar *flow-record-origins* nil)
(defvar *flow-defer-source-call* nil)
(defvar *effective-return-proof* nil)
;; A CEM uses the shared source grammar. Only CALL-METHOD leaves belong to
;; the MOP composer; their code/value receipt is supplied at evaluation time.
(defvar *effective-method-emitter* nil)
(defvar *fixed-effective-arguments* nil)
(defvar *collect-function-flow* nil)
(defvar *function-flow-changed* nil)
;; Unknown inputs for otherwise uncalled selected method roots enter only
;; after the ordinary caller fixed point has quiesced.
(defvar *settled-method-roots* nil)
;; The value-producing expression of one enclosing audited indirect callee.
;; Propagate by syntactic position, never by collecting shared FUNCTION nodes.
(defvar *immediate-callee-value* nil)
(defvar *value-domain-local-functions* nil)
(defvar *local-function-frames* nil)
(defvar *local-function-scope-cache* nil)
(defvar *declared-specials* nil)
(defvar *mutable-invariant-bindings* nil)
(defvar *tagbody-targets* nil)
(defvar *immediate-lambda-domains* nil)
;; Only source-owned cold global initializers may emit fresh symbol recipes.
(defvar *cold-global-initializer* nil)
(defvar *cold-method-combination-factory* nil)
(defvar *cold-recipe-source-nodes* nil)
(defvar *cold-recipe-source-marker* nil)
(defvar *cold-recipe-normalization* nil)
(defvar *reproducible-source-expansion* nil)
(defvar *cold-recipe-active* nil)
(defvar *cold-recipe-functions* nil)

(defparameter *standard-slot-setter-function* (fdefinition 'sb-pcl::set-slot-value))

(defparameter *standard-miss-methods*
  (loop for (name specializers) in '((no-next-method (standard-generic-function standard-method))
                                    (no-applicable-method (t)))
        for method = (find-method (fdefinition name) nil (mapcar #'find-class specializers))
        collect (list name method (sb-mop:method-function method))))

(defparameter *standard-initialization-methods*
  (loop for (name specializers) in '((initialize-instance (sb-pcl::slot-object))
                                    (shared-initialize (sb-pcl::slot-object t))
                                    (allocate-instance (standard-class)))
        for method = (find-method (fdefinition name) nil (mapcar #'find-class specializers))
        collect (list name method (sb-mop:method-function method))))

(defparameter *standard-construction-methods*
  (loop for specializer in '(symbol class)
        for method = (find-method #'make-instance nil (list (find-class specializer)))
        collect (list specializer method (sb-mop:method-function method))))

(defparameter *standard-initarg-functions*
  (loop for name in '(sb-pcl::check-mi-initargs sb-pcl::check-initargs-1
                     sb-pcl::check-initargs-values sb-pcl::check-initargs-2-plist
                     sb-pcl::initarg-error)
        collect (cons name (fdefinition name))))

(defparameter *standard-slot-methods*
  (loop for (name arity) in '((slot-missing 4) (slot-unbound 3))
        for method = (find-method (fdefinition name) nil
                                  (make-list arity :initial-element (find-class t)))
        collect (list name method (sb-mop:method-function method))))

(defparameter *standard-class-applicability-method*
  (let ((method (find-method #'sb-mop:compute-applicable-methods-using-classes nil
                            (list (find-class 'generic-function) (find-class t)))))
    (list method (sb-mop:method-function method))))

(defparameter *standard-slot-functions*
  (loop for name in '(sb-int:read-evaluated-form sb-ext:print-symbol-with-prefix)
        collect (cons name (fdefinition name))))

(defparameter *record-runtime-functions*
  (loop for name in '(snowgrave:make-layout snowgrave:make-reference-domain snowgrave:sg-make-record
                     snowgrave:sg-record-p snowgrave:sg-record-class
                     snowgrave:sg-record-layout-p snowgrave:sg-record-matches-layout-p snowgrave:sg-record-typep
                     snowgrave:sg-record-unit-p snowgrave:sg-record-read
                     (setf snowgrave:sg-record-read) snowgrave:sg-record-write
                     snowgrave:sg-record-boundp snowgrave:sg-record-unbind
                     snowgrave:sg-domain-violation snowgrave::%record-read
                     (setf snowgrave::%record-read) snowgrave::%record-write
                     snowgrave::%record-boundp snowgrave::%record-unbind)
        collect (cons name (fdefinition name))))

(defstruct literal-pool
  name
  (indices (make-hash-table :test #'eq))
  (values (make-array 0 :adjustable t :fill-pointer 0)))

(defstruct build
  identity source declaration open-package output-package
  layouts generated constructors method-names reference-domain-name layout-names
  normalized-forms
  (normalized-originals (make-hash-table :test #'eq))
  (sequence 0) (dependencies nil) (source-key nil) (integer-constants nil)
  (literal-pools nil)
  (literal-states (make-hash-table :test #'eq))
  function-domains function-returns generic-call-shapes function-flow-evidence function-values
  (graph-index (make-hash-table :test #'eq))
  graph-nodes graph-imports graph-root-names graph-root-references graph-resource-name
  graph-state-invalidations
  (graph-field-envelopes (make-hash-table :test #'equal))
  (graph-field-writes (make-hash-table :test #'eq))
  (source-origins (make-hash-table :test #'eq))
  (source-array-copies (make-hash-table :test #'eq))
  (graph-literal-states (make-hash-table :test #'eq)))

(defun build-forms (build)
  (or (build-normalized-forms build) (snowgrave:authored-source-forms (build-source build))))
(defun build-classes (build) (snowgrave:authored-source-names (build-source build) :class))
(defun build-generics (build) (snowgrave:authored-source-names (build-source build) :generic))
(defun build-functions (build) (snowgrave:authored-source-names (build-source build) :function))
(defun build-globals (build) (snowgrave:authored-source-names (build-source build) :global))
(defun build-method-sources (build)
  (remove-if-not (lambda (form) (eq (defining-kind form) :method)) (build-forms build)))
(defun authored-source-key (build form)
  (list (build-identity build) (snowgrave:authored-form-position
                                (build-source build)
                                (gethash form (build-normalized-originals build) form))))

(defun fail (build type feature detail &optional (phase :source-admission))
  (snowgrave::reject type phase feature detail
                     :source-key (build-source-key build)
                     :path (list (build-identity build))))

(defmacro with-build-source-key ((build key) &body body)
  (let ((owner (gensym "SOURCE-OWNER")) (previous (gensym "SOURCE-KEY")))
    `(let* ((,owner ,build) (,previous (build-source-key ,owner)))
       (unwind-protect (progn (setf (build-source-key ,owner) ,key) ,@body)
         (setf (build-source-key ,owner) ,previous)))))

(defun normalized-definition-form (build definition)
  (let ((original (snowgrave:authored-definition-form definition)))
    (or (find original (build-normalized-forms build)
              :key (lambda (form) (gethash form (build-normalized-originals build))))
        original)))

(defun normalization-environment (build)
  ;; Authored global functions shadow host macros just as their pass-one
  ;; definitions will. Local MACROLET/FLET environments extend this boundary.
  (sb-cltl2:augment-environment
   nil :function (append (build-functions build) (build-generics build))))

(defun normalize-source-expression (build expression &optional environment)
  "Expand ordinary host macros once, retaining the adapter's audited syntax.
The host walker owns lexical environments and binders, including macro lambda
lists and &ENVIRONMENT. This is not a second implementation of LOOP. Macros
which already have semantic lowering retain their places, keys and binders;
all other expansions re-enter the same admission and residual audits."
  (let ((global-environment (normalization-environment build))
        (sb-walker::*walk-form-expand-macros-p* t)
        (wrapper nil))
    (labels
        ((walk (form env) (sb-walker:walk-form form env #'visit))
         (body (forms env)
           (multiple-value-bind (prefix executable) (snowgrave::source-body-parts forms)
             (append prefix (mapcar (lambda (form) (walk form env)) executable))))
         (bound-body (variables forms env)
           ;; A synthetic lambda delegates declaration/binding shadowing to
           ;; the host; only its normalized body is retained.
           (cddr (walk `(lambda ,variables ,@forms) env)))
         (visit (form context env)
           (when (and (or *cold-recipe-normalization* *reproducible-source-expansion*)
                      (eq context :eval))
             (audit-cold-recipe-macro build form env))
           (when (and (consp form) (eq (car form) 'declare)
                      (or *cold-recipe-normalization*
                          (and *cold-recipe-source-nodes* (gethash form *cold-recipe-source-nodes*))))
             (audit-cold-recipe-form build form nil))
           (cond
             ((and *cold-recipe-source-nodes* (eq context :eval)
                   (gethash form *cold-recipe-source-nodes*)
                   (or (consp form)
                       (and (symbolp form)
                            (multiple-value-bind (kind localp) (sb-cltl2:variable-information form env)
                              (or (eq kind :special) (not localp))))))
              (let ((*cold-recipe-source-nodes* nil) (*cold-recipe-normalization* t))
                (values (list *cold-recipe-source-marker* (walk form env)) t)))
             ((or (not (eq context :eval)) (atom form)) form)
             ((and (member (car form) '(macrolet symbol-macrolet)) (not (eq form wrapper)))
              ;; Let the host establish the local definitions, then discard
              ;; compile-time wrappers. Their expanded executable bodies are
              ;; the only inputs to either materialization pass.
              (let* ((previous wrapper)
                     (normalized (unwind-protect (progn (setf wrapper form) (walk form env))
                                   (setf wrapper previous))))
                (values `(locally ,@(cddr normalized)) t)))
             ((and *effective-method-emitter* (eq (car form) 'call-method))
              ;; METHOD objects and the literal next-method list are compiler
              ;; inputs, not ordinary source values. MAKE-METHOD's body still
              ;; belongs to this lexical normalization environment.
              (let ((method (second form)))
                (values
                 (if (and (consp method) (eq (first method) 'make-method))
                     `(call-method (make-method ,(walk (second method) env)) ,@(cddr form))
                     form) t)))
             ((and *effective-method-emitter* (eq (car form) 'sb-pcl::call-method-list))
              (values (walk `(progn ,@(cdr form)) env) t))
             ((eq (car form) 'load-time-value)
              (values `(load-time-value ,(walk (second form) global-environment) ,@(cddr form)) t))
             ((member (car form) '(setf incf decf push pushnew pop multiple-value-setq))
              (values
               (case (car form)
                 (multiple-value-setq `(multiple-value-setq ,(second form) ,(walk (third form) env)))
                 (otherwise (cons (car form) (mapcar (lambda (part) (walk part env)) (cdr form))))) t))
             ((member (car form) '(and or when unless))
              (values (cons (car form) (mapcar (lambda (part) (walk part env)) (cdr form))) t))
             ((eq (car form) 'cond)
              (values `(cond ,@(mapcar (lambda (clause)
                                        (mapcar (lambda (part) (walk part env)) clause))
                                        (conditional-clauses build form))) t))
             ((member (car form) '(case ecase))
              (values `(,(car form) ,(walk (second form) env)
                         ,@(mapcar (lambda (clause) (cons (car clause) (body (cdr clause) env)))
                                   (case-clauses build form))) t))
             ((eq (car form) 'multiple-value-bind)
              (values `(multiple-value-bind ,(second form) ,(walk (third form) env)
                         ,@(bound-body (second form) (cdddr form) env)) t))
             ((eq (car form) 'destructuring-bind)
              ;; The admitted destructuring profile has required bindings;
              ;; the shared portable owner still validates its exact grammar.
              (let ((variables (required-binding-variables build form)))
                (values `(destructuring-bind ,(second form) ,(walk (third form) env)
                           ,@(bound-body variables (cdddr form) env)) t)))
             ((eq (car form) 'handler-case)
              (values `(handler-case ,(walk (second form) env)
                         ,@(mapcar (lambda (clause)
                                     (list* (car clause) (second clause)
                                            (bound-body (handler-binding-variables build clause) (cddr clause) env)))
                                   (cddr form))) t))
             ((eq (car form) 'handler-bind)
              (values `(handler-bind
                           ,(mapcar (lambda (binding) (list (first binding) (walk (second binding) env)))
                                    (second form))
                         ,@(body (cddr form) env)) t))
             ;; The host's LOOP collector emits a stack-allocation hint, not
             ;; a client ABI. Its documented source transform is (LIST arg).
             ;; Lower that exact primitive, never allow arbitrary SB-* calls.
             ((eq (car form) 'sb-kernel:unaligned-dx-cons)
              (unless (= (length form) 2)
                (fail build 'snowgrave:unsupported-definition :host-normalization
                      "Unexpected host cons primitive shape."))
              (values `(list ,(walk (second form) env)) t))
             ((and (member (car form) '(rplaca rplacd)) (= (length form) 3))
              ;; Reuse the existing ordinary-place audit while preserving both
              ;; argument evaluations and RPLACx's original-cons result.
              (let ((cell (gensym "CONS-CELL")) (value (gensym "CONS-VALUE")))
                (values (walk `(let ((,cell ,(second form)) (,value ,(third form)))
                                 (setf (,(if (eq (car form) 'rplaca) 'car 'cdr) ,cell) ,value)
                                 ,cell) env) t)))
             ((and (eq (car form) 'sb-pcl::set-slot-value)
                   (not (nth-value 1 (sb-cltl2:function-information (car form) env)))
                   (standard-operation-meaning-p build (car form))
                   (fboundp (car form))
                   (eq (fdefinition (car form)) *standard-slot-setter-function*))
              ;; The host's generalized-place expansion (ROTATEF, SHIFTF,
              ;; etc.) uses object/name/value order for this exact setter.
              ;; Return to the shared SLOT-VALUE place owner, preserving that
              ;; order and every effect instead of admitting a native CLOS call.
              (unless (= (length form) 4)
                (fail build 'snowgrave:unsupported-definition :host-slot-setter-shape
                      "The pinned host slot setter requires object, slot name and value."))
              (values (walk `(setf (slot-value ,(second form) ,(third form)) ,(fourth form)) env) t))
             ((eq (car form) 'sb-kernel:the*)
              ;; SBCL supplies a walker macrofunction even though THE* is a
              ;; special operator. USE-ANNOTATIONS is PROGN, not a LIST cast.
              ;; Other profiles can lose secondary values or error context;
              ;; only the annotation-only, context-free profile is admitted.
              (destructuring-bind
                  (operator (type &key context silent-conflict derive-type-only
                                       truly source-form use-annotations restart) operand) form
                (declare (ignore operator silent-conflict source-form operand))
                (when (or (not use-annotations) context derive-type-only truly restart)
                  (fail build 'snowgrave:unsupported-definition :host-annotation-options
                        "This THE* option profile has no equivalent admitted walker expansion."))
                (unless (or (native-value-type-p type) (member type '(t list cons)))
                  (fail build 'snowgrave:unsupported-definition :host-annotation-type
                        "THE* needs an admitted native type; arbitrary type expanders are not a normalization contract."))
                (multiple-value-bind (expansion expandedp) (macroexpand-1 form env)
                  (unless expandedp
                    (fail build 'snowgrave:unsupported-definition :host-normalization
                          "This host does not supply THE*'s walker expansion."))
                  (values (walk expansion env) t))))
             ((eq (car form) 'sb-ext:truly-the)
              (values `(the ,(second form) ,(walk (third form) env)) t))
             ((and (symbolp (car form)) (not (eq (car form) 'lambda))
                   (not (special-operator-p (car form))) (macro-function (car form) env))
              ;; Explicitly retain this expansion result. WALK-FORM otherwise
              ;; may reconstruct the authored macro when no child changes.
              (multiple-value-bind (expansion expandedp) (macroexpand-1 form env)
                (if expandedp (values (walk expansion env) t) form)))
             (t form))))
      (handler-case (walk expression (or environment global-environment))
        (snowgrave:snowgrave-error (condition) (error condition))
        (error (condition)
          (fail build 'snowgrave:unsupported-definition :host-macroexpansion
                (format nil "Host lexical normalization failed: ~A" condition)))))))

(defun normalize-authored-definition (build form)
  (labels ((expression (value) (normalize-source-expression build value))
           (lambda-form (lambda-list body)
             (expression `(lambda ,lambda-list ,@body))))
    (case (defining-kind form)
      (:function
       (let ((normalized (lambda-form (third form) (cdddr form))))
         (list* (car form) (second form) (second normalized) (cddr normalized))))
      (:method
       (multiple-value-bind (qualifiers lambda-list body) (method-parts form)
         (let* ((requiredp t)
                (ordinary (mapcar (lambda (item)
                                    (when (member item lambda-list-keywords) (setf requiredp nil))
                                    (if (and requiredp (consp item)) (first item) item)) lambda-list))
                (normalized (lambda-form ordinary body))
                (requiredp t)
                (normalized-list
                  (loop for original in lambda-list for item in (second normalized)
                        do (when (member original lambda-list-keywords) (setf requiredp nil))
                        collect (if (and requiredp (consp original)) original item))))
           `(,(car form) ,(second form) ,@qualifiers ,normalized-list ,@(cddr normalized)))))
      (:class
       `(,(car form) ,(second form) ,(third form)
         ,(mapcar (lambda (slot)
                    (if (symbolp slot) slot
                        (cons (car slot) (loop for (key value) on (cdr slot) by #'cddr
                                               append (list key (if (eq key :initform) (expression value) value))))))
                  (fourth form))
         ,@(mapcar (lambda (option)
                     (if (eq (car option) :default-initargs)
                         (cons (car option) (loop for (key value) on (cdr option) by #'cddr
                                                  append (list key (expression value)))) option)) (cddddr form))))
      (:global
       (if (> (length form) 2)
           (list* (car form) (second form) (expression (third form)) (cdddr form)) form))
      (t form))))

(defun source-copy-observer (build &optional snapshotp)
  ;; Transient ownership provenance joins native literals with captured roots.
  ;; Syntax is still copied on every boundary; no source handle is retained in
  ;; the installed unit or in its serialized metadata.
  (when (entry-graph-request-p build)
    (lambda (original copy)
      (let ((origin (gethash original (build-source-origins build) original)))
        (setf (gethash copy (build-source-origins build)) origin)
        ;; Only the frozen normalized output defines candidate literal data
        ;; at the capture cut. Keep pointers, never another payload copy.
        (when (and snapshotp (arrayp origin))
          (push copy (gethash origin (build-source-array-copies build))))))))

(defun normalize-authored-source (build)
  ;; Neither a user expander that destructively edits its argument nor a
  ;; returned, globally aliased expansion can mutate the authored provenance
  ;; or the pass-two input. Own both graphs, preserving literal EQ sharing.
  (let* ((originals (snowgrave:authored-source-forms (build-source build)))
         (inputs (snowgrave::immutable-copy originals (source-copy-observer build)))
         (expanded (loop for original in originals for input in inputs
                         collect (with-build-source-key (build (authored-source-key build original))
                                   (normalize-authored-definition build input))))
         (frozen (snowgrave::immutable-copy expanded (source-copy-observer build t))))
    (loop for original in originals for normalized in frozen
          do (setf (gethash normalized (build-normalized-originals build)) original))
    ;; Every pass and every return/call analysis consumes this same snapshot.
    (setf (build-normalized-forms build) frozen)))

(defun name= (a b)
  (labels ((namep (x)
             (or (and (symbolp x) (symbol-package x))
                 (and (consp x) (eq (car x) 'setf) (= (length x) 2) (symbolp (cadr x))))))
    (and (namep a) (namep b)
         (equal (snowgrave::function-name-key a) (snowgrave::function-name-key b)))))

(defun member-name (name names)
  (member name names :test #'name=))

(defun mapped-name (name package)
  (if (consp name)
      (list 'setf (mapped-name (cadr name) package))
      (if (eq (symbol-package name) package) name
          (intern (with-standard-io-syntax
                    (write-to-string (snowgrave::function-name-key name))) package))))

(defun initialization-generic-p (name)
  (member name '(initialize-instance shared-initialize)))

(defun open-generic (build name)
  (fdefinition (if (initialization-generic-p name) name
                  (mapped-name name (build-open-package build)))))

(defun fixed-generic-arity (build name)
  "Return the minimum and maximum finite positional arities, or NIL.
The actual MOP still selects and combines every method. Rest/key contracts
retain the ordinary parser path; AUX and optional defaults stay method-local."
  (when (and (member-name name (getf (build-declaration build) :closed-generics))
             (not (initialization-generic-p name)))
    (let ((gf (open-generic build name)))
      (labels ((finitep (lambda-list &optional method)
                 (let ((contract (lambda-contract build lambda-list :method method)))
                   (not (or (getf contract :rest) (getf contract :keyp))))))
        (when (and (finitep (sb-mop:generic-function-lambda-list gf))
                   (every (lambda (method) (finitep (sb-mop:method-lambda-list method) t))
                          (sb-mop:generic-function-methods gf)))
          (let* ((contract (lambda-contract build (sb-mop:generic-function-lambda-list gf)))
                 (required (length (getf contract :required))))
            (values required (+ required (length (getf contract :optional))))))))))

(defun fixed-generic-name (build name)
  (if (consp name) (list 'setf (fixed-generic-name build (cadr name)))
      (intern (concatenate 'string "%FIXED-GENERIC/"
                           (with-standard-io-syntax
                             (write-to-string (snowgrave::function-name-key name))))
              (build-output-package build))))

(defun direct-call-name (build name package open local argument-count)
  ;; Resolve/audit the public binding before choosing its internal convention.
  ;; FUNCTION captures still use TRANSFORMED-FUNCTION-NAME and keep identity.
  (let ((public (transformed-function-name build name package open local)))
    (multiple-value-bind (minimum maximum)
        (unless (or open (member-name name local)) (fixed-generic-arity build name))
      (if (and minimum (<= minimum argument-count maximum))
          (values (fixed-generic-name build name) t
                  (if (= minimum maximum) '(nil)
                      (append (make-list (- maximum argument-count))
                              (list argument-count nil))))
          (values public nil nil)))))

(defun fixed-invocation-argument-plan (build form)
  ;; Literal VALUES has source expressions at every ordered position. Other
  ;; MVC producers retain the ordinary emitted MULTIPLE-VALUE-BIND plan.
  (if (and (eq (first form) 'multiple-value-call)
           (every (lambda (producer) (and (consp producer) (eq (first producer) 'values))) (cddr form)))
      (multiple-value-bind (arguments bindings domains completep)
          (multiple-value-call-plan build (cddr form))
        (declare (ignore bindings domains)) (values arguments nil completep))
      (ordinary-call-argument-plan build form)))

(defun emit-fixed-generic-invocation (build callee arguments targets globals)
  "Realize a proved finite invocation without changing its public identities.
The source callee and every primary argument are evaluated exactly once, in
order, before an identity choice. Unknown/nonkernel targets keep FUNCALL."
  (let ((plans nil) (count (length arguments)))
    (dolist (target targets)
      (when (and (not (local-function-binding-p target)) (member-name target globals))
        (multiple-value-bind (minimum maximum) (fixed-generic-arity build target)
          (when (and minimum (<= minimum count maximum))
            (push (list target (if (= minimum maximum) '(nil)
                                  (append (make-list (- maximum count)) (list count nil)))) plans)))))
    (when plans
      (let ((function (fresh-name build "FIXED-CALLEE"))
            (parameters (loop repeat count collect (fresh-name build "FIXED-ARG"))))
        `(let* ((,function ,callee)
                ,@(mapcar #'list parameters arguments))
           (cond ,@(loop for (target suffix) in (nreverse plans)
                         collect `((eq ,function #',(mapped-name target (build-output-package build)))
                                   (funcall #',(fixed-generic-name build target) ,@parameters ,@suffix)))
                 (t (funcall ,function ,@parameters))))))))

(defun fixed-effective-error-arguments (parameters)
  ;; Only an error path materializes the original positional tuple. Padding
  ;; slots never become arguments, and supplied NIL remains a real argument.
  (if (consp *fixed-effective-arguments*)
      (destructuring-bind (arguments count minimum maximum) *fixed-effective-arguments*
        `(or ,arguments
             (case ,count
               ,@(loop for arity from minimum to maximum
                       collect `(,arity (list ,@(subseq parameters 0 arity)))))))
      `(list ,@parameters)))

(defun fixed-effective-method-body (build generic method ordinary body parameters)
  ;; One ordinary method body/default binder is shared by every positional
  ;; shape. The lexical function does not escape; CALL-NEXT retains the outer
  ;; transport tuple, including its actual count, rather than defaulted values.
  (if (consp *fixed-effective-arguments*)
      (destructuring-bind (arguments count minimum maximum) *fixed-effective-arguments*
        (let ((name (fresh-name build "POSITIONAL-METHOD"))
              (surplusp (method-positional-surplus-p build method)))
          (when surplusp (audit-method-positional-parser-inputs build generic method))
          `(flet ((,name ,ordinary ,@body))
             (case ,count
               ,@(loop for arity from minimum to maximum
                       collect `(,arity (,name ,@(subseq parameters 0 arity))))
               (t ,(if surplusp
                       (destructuring-bind (class control) (positional-surplus-schema build)
                         `(error ',class :format-control ,control
                                        :format-arguments (list (nthcdr ,maximum ,arguments))))
                       `(apply #',name ,arguments)))))))
      `(,(if *fixed-effective-arguments* 'funcall 'apply)
        (lambda ,ordinary ,@body)
        ,@(if *fixed-effective-arguments* parameters (list (car parameters))))))

(defun source-specials (build)
  (snowgrave:authored-source-specials (build-source build)))

(defun special-variable-p (build name)
  ;; A known initializer never seals a dynamic binding against an admitted
  ;; external operation. Host proclamations also affect authored parameters
  ;; and LET bindings, even when the proclamation is outside this source unit.
  (and (symbolp name)
       (or (member name (source-specials build))
           (member name *declared-specials*)
           (eq (sb-int:info :variable :kind name) :special))))

(defun global-binding-name (build symbol package open)
  (declare (ignore open))
  (if (member symbol (source-specials build)) symbol
      (mapped-name symbol package)))

(defun source-name (name)
  (if (symbolp name) (symbol-name name) (symbol-name (cadr name))))

(defun read-source (source)
  (cond
    ((and (consp source) (eq (car source) :forms))
     (cadr source))
    ((and (consp source) (eq (car source) :files))
     (let ((forms nil) (*package* *package*) (*read-eval* nil))
       (dolist (file (cdr source))
         (with-open-file (stream file)
           (loop for form = (read stream nil stream)
                 until (eq form stream)
                 do (cond
                      ((and (consp form) (eq (car form) 'in-package))
                       (let ((package (find-package (cadr form))))
                         (unless package
                           (snowgrave::reject
                            'snowgrave:unsupported-definition :source-admission
                            :source-package
                            "For :FILES, declare source packages before closing; definitions are isolated."))
                         (setf *package* package)))
                      ((and (consp form) (eq (car form) 'defpackage)) nil)
                      (t (push form forms))))))
       (nreverse forms)))
    (t (snowgrave::reject 'snowgrave:unsupported-definition :source-admission
                         :source-unit
                         "This adapter accepts (:FORMS ordered-forms) and (:FILES pathname ...)."))))

(defun defining-kind (form) (snowgrave:source-defining-kind form))

(defun index-source (build)
  ;; The portable source owner supplies identity, order and duplicate checks.
  ;; Only host/environment-specific admission belongs in this adapter.
  (dolist (definition (snowgrave:authored-source-definitions (build-source build)))
    (let ((form (normalized-definition-form build definition))
          (name (snowgrave:authored-definition-name definition)))
      (setf (build-source-key build) (authored-source-key build form))
      (case (snowgrave:authored-definition-kind definition)
        (:class
         (let ((common-name (find-symbol (symbol-name name) :cl)))
           (when (and common-name (find-class common-name nil))
             (fail build 'snowgrave:unsupported-definition :class-name-collision
                   "This adapter rejects authored class names that shadow Common Lisp classes."))))
        (:generic
         (when (initialization-generic-p name)
           (fail build 'snowgrave:unsupported-definition :initialization-generic-definition
                 "Host initialization protocol definitions are supplied by the adapter, not redefined.")))
        (:method
         (when (member name '(make-instance allocate-instance reinitialize-instance
                             slot-missing slot-unbound no-applicable-method no-next-method
                             change-class update-instance-for-redefined-class
                             update-instance-for-different-class))
           (fail build 'snowgrave:unclosed-class-operation :authored-native-protocol
                 "This authored native protocol requires its own effective-method/error materialization; it cannot enter an unused private generic.")))
        (:global
         (when (and (member (car form) '(defvar defparameter)) (constantp name))
           (fail build 'snowgrave:unsupported-definition :constant-special-name
                 "An authored special variable cannot redefine an existing constant."))))))
  (let ((decl (build-declaration build)))
    (dolist (name (getf decl :closed-classes))
      (unless (member-name name (build-classes build))
        (fail build 'snowgrave:unsupported-definition :class-provenance
              (format nil "Class ~S has no wrapped definition in the source unit." name))))
    (dolist (name (getf decl :closed-generics))
      (unless (or (initialization-generic-p name)
                  (member-name name (build-generics build))
                  ;; Accessor generics are authored by a wrapped class.
                  (some (lambda (form)
                          (and (eq (defining-kind form) :class)
                               (some (lambda (slot)
                                       (and (consp slot)
                                            (loop for (option value) on (cdr slot) by #'cddr
                                                  thereis (and (member option '(:reader :writer :accessor))
                                                               (or (name= name value)
                                                                   (and (eq option :accessor)
                                                                        (name= name (list 'setf value))))))))
                                     (fourth form))))
                        (build-forms build)))
        (fail build 'snowgrave:unsupported-definition :generic-provenance
              (format nil "Generic ~S has no wrapped definition or accessor provenance." name))))
    (unless (and (every (lambda (name) (member-name name (getf decl :closed-classes)))
                       (build-classes build))
                 (every (lambda (name) (member-name name (getf decl :closed-generics)))
                        (build-generics build)))
      (fail build 'snowgrave:unsupported-definition :unselected-definition
            "All authored classes and generic functions must join this initial cohort."))
    (dolist (entry (getf decl :entries))
      (unless (member-name entry (build-functions build))
        (fail build 'snowgrave:unsupported-definition :entry
              "External entries must name authored ordinary functions.")))))

(defparameter *ordinary-operations*
  '(+ - * / 1+ 1- = /= < > <= >= zerop plusp minusp max min abs mod rem floor
    ceiling truncate round ash logand logior logxor lognot integer-length evenp oddp
    values values-list list list* cons car cdr caar cadr cdar cddr first second
    third fourth rest nth nthcdr endp null not atom consp symbolp numberp
    integerp rationalp floatp realp complexp stringp characterp vectorp arrayp
    eq eql equal equalp identity vector length reverse nreverse append copy-list
    copy-tree member assoc getf gethash remhash aref svref sbit bit char
    subseq concatenate mapcar mapc maplist mapcan reduce find position count
    remove remove-if delete delete-if sort stable-sort copy-seq fill coerce
    make-array make-hash-table make-string string string= string-equal
    symbol-name keywordp char-code code-char format princ prin1 print terpri
    error signal warn break cerror invoke-restart find-restart abort
    condition-name type-error-datum type-error-expected-type
    unbound-slot-instance cell-error-name))

(defparameter *reproducible-global-operations*
  '(list list* cons vector make-array))

(defparameter *reproducible-integer-operations*
  ;; Each result is an integer when every argument is an integer. The host
  ;; still owns arity, exceptional inputs and secondary values. No floating
  ;; arithmetic environment or ambient variable is part of this grammar.
  '(+ - * 1+ 1- min max abs mod rem floor ceiling truncate round ash
    logand logior logxor lognot integer-length))

(defparameter *standard-integer-constants*
  ;; Only actual COMMON-LISP constant bindings enter this host ABI snapshot.
  ;; An arbitrary ambient DEFCONSTANT/CONSTANTP is not source provenance.
  (let ((constants nil))
    (do-external-symbols (name :common-lisp)
      (when (and (eq (symbol-package name) (find-package :common-lisp))
                 (eq (sb-int:info :variable :kind name) :constant)
                 (boundp name) (integerp (symbol-value name)))
        (push (cons name (symbol-value name)) constants)))
    constants))

(defparameter *representation-sensitive-ordinary-operations*
  ;; These standard operators observe logical values or invoke callbacks. Their
  ;; contract follows the actual finite callee, independent of call syntax.
  '(gethash remhash make-hash-table mapcar mapc maplist mapcan reduce remove-if
    delete-if sort stable-sort member assoc find position count remove delete
    format princ prin1 print fill coerce length))

(defparameter *native-ordinary-functions*
  ;; Restricted compiler/runtime boundary. SYS provenance alone would also
  ;; admit reflective evaluators and open PCL dispatch helpers. These names
  ;; cover the admitted ordinary operations and the compiler's materialized
  ;; error, list append and destructuring contracts.
  (loop for name in (append *ordinary-operations*
                           '(apply typep get-properties write-string write-char
                             ;; COERCE's compiler expansion copies between the
                             ;; audited built-in sequences via ordinary REPLACE.
                             replace sb-kernel:vector-to-list sb-int:%simple-error
                             sb-kernel:with-simple-condition-restarts
                             ;; Constant negative ASH selects the checked
                             ;; integer/bignum shift leaf (numbers.lisp).
                             sb-kernel:ash-right
                             ;; Materialized integer bitwise operations use
                             ;; these checked two-argument specializations.
                             sb-kernel:two-arg-and sb-kernel:two-arg-ior sb-kernel:two-arg-xor
                             sb-kernel:%member-eq
                             ;; Actual SBCL list/sequence specialization helpers
                             ;; for the audited ordinary operators. Their host
                             ;; runtime boundary is not target residency proof.
                             sb-kernel:%assoc-eq sb-kernel:%find-position sb-int:delq
                             sb-kernel:two-arg-string-equal
                             ;; SEQTRAN's FILL specializations for ordinary data.
                             sb-kernel:list-fill sb-kernel:vector-fill
                             ;; Compiler-selected, bounds-checked AREF for a
                             ;; general vector (including adjustable/string).
                             sb-kernel:vector-hairy-data-vector-ref/check-bounds
                             ;; SEQTRAN's REVERSE rewrite-full-call selects
                             ;; these ordinary LIST/VECTOR implementations.
                             ;; LIST-REVERSE is the ENDP/POP/PUSH cons loop.
                             sb-impl::list-reverse sb-impl::vector-reverse
                             sb-impl::append2 sb-c::check-ds-list/&rest))
        when (fboundp name) collect (cons name (fdefinition name))))

(defun quoted-value (form)
  (when (and (consp form) (eq (car form) 'quote) (= (length form) 2))
    (values (cadr form) t)))

(defun function-target-p (build name local)
  (or (member-name name local)
      (member-name name (build-functions build))
      (member-name name (getf (build-declaration build) :closed-generics))
      (member-name name (getf (build-declaration build) :external-operations))
      (and *generated-class-operation* (member name '(snowgrave:sg-record-read snowgrave:sg-record-write snowgrave::%record-read snowgrave::%record-write)))
      (member name *ordinary-operations*)))

(defun transformed-function-name (build name package open local)
  ;; Direct calls, FUNCTION captures and generalized SETF places share the
  ;; same binding decision. A declared external or lexical operation retains
  ;; its real identity; only authored closed cohort definitions are renamed.
  ;; Open code runs only in the disposable host world. Its binding isolation
  ;; is still required, but deployed target admission and dependencies belong
  ;; to the closed cohort discovered afterward, including non-entry roots.
  (when (and open *cold-method-combination-factory* *cold-recipe-functions*
             (not (member-name name local)) (ordinary-function-form build name))
    (audit-cold-source-function build name))
  (unless open
    (unless (function-target-p build name local)
      (fail build 'snowgrave:unclosed-call :call-target
            (format nil "Call or function capture of undeclared operation ~S." name)))
    (pushnew (snowgrave::function-name-key name) (build-dependencies build) :test #'equal))
  (if (and (not (member-name name local))
           (or (member-name name (build-functions build))
               (member-name name (getf (build-declaration build) :closed-generics))))
      (if (and open (initialization-generic-p name)) name (mapped-name name package)) name))

(defun native-value-type-p (domain)
  "A standard type whose values cannot contain a rewritten record/callable.
No arbitrary type alias, pointer array, or foreign class is an owner ABI."
  (unless (or (atom domain) (snowgrave::source-finite-list-p domain))
    (return-from native-value-type-p nil))
  (handler-case
   (labels ((scalar (type)
             (unless (or (atom type) (snowgrave::source-finite-list-p type))
               (return-from scalar nil))
             (or (member type '(number integer rational ratio real complex float
                                short-float single-float double-float long-float
                                fixnum bignum symbol null keyword boolean character
                                base-char standard-char string base-string simple-string
                                simple-base-string bit-vector simple-bit-vector))
                 (and (consp type) (snowgrave::source-finite-list-p type)
                      (member (car type) '(integer rational real float short-float single-float
                                          double-float long-float signed-byte unsigned-byte mod
                                          string base-string simple-string simple-base-string
                                          bit-vector simple-bit-vector))
                      (every (lambda (part)
                               (or (numberp part) (eq part '*)
                                   (and (consp part) (null (cdr part)) (numberp (car part))))) (cdr type)))
                 (and (consp type) (eq (car type) 'eql) (= (length type) 2)
                      (or (numberp (second type)) (symbolp (second type)) (characterp (second type)))))))
    (and (or (scalar domain)
             (and (consp domain) (snowgrave::source-finite-list-p domain) (eq (car domain) 'or)
                  (cdr domain) (every #'native-value-type-p (cdr domain)))
             (and (consp domain) (snowgrave::source-finite-list-p domain)
                  (member (car domain) '(array simple-array)) (= (length domain) 3)
                  (scalar (second domain))
                  ;; Scalar-valued specialized storage cannot acquire a
                  ;; hidden record by alias mutation. T/pointer arrays cannot
                  ;; make this claim, even if a constructor once filled NIL.
                  (let ((upgraded (upgraded-array-element-type (second domain))))
                    (or (subtypep upgraded 'number) (subtypep upgraded 'character)))
                  (let ((dimensions (third domain)))
                    (or (eq dimensions '*)
                        (and (integerp dimensions) (<= 0 dimensions))
                        (and (snowgrave::source-finite-list-p dimensions)
                             (every (lambda (size) (or (eq size '*) (and (integerp size) (<= 0 size)))) dimensions))))))
         ;; Validate the complete standard type grammar through the host. The
         ;; classifier above never invokes a user DEFTYPE or SATISFIES owner.
         (progn (typep nil domain) t)))
   (error () nil)))

(defun shaped-domain-p (domain)
  ;; An internal product in the existing flow lattice, never a public CL type.
  (and (consp domain) (eq (car domain) :shaped)
       (snowgrave::source-finite-list-p domain) (= (length domain) 3)
       (eq (third domain) :external-result)))

(defun external-result-domain-p (domain)
  (when (relational-value-domain-p domain)
    (return-from external-result-domain-p (external-result-domain-p (third domain))))
  (or (eq domain :external-result) (shaped-domain-p domain)
      (and (graph-node-domain-p domain) (external-result-domain-p (third domain)))
      (and (consp domain) (eq (car domain) 'or) (some #'external-result-domain-p (cdr domain)))))

(defun qualify-domain-origin (shape origin)
  ;; A shape establishes geometry, not an aggregate's element representation.
  (if (external-result-domain-p origin)
      (if (eq shape :unknown) :external-result (list :shaped shape :external-result))
      shape))

(defun value-domain-shape (build domain)
  (when (relational-value-domain-p domain)
    (return-from value-domain-shape (value-domain-shape build (third domain))))
  (cond ((initializing-record-domain-p domain) (third domain))
        ((owned-record-domain-p domain) (second domain))
        ((graph-node-domain-p domain) (value-domain-shape build (third domain)))
        ((shaped-domain-p domain) (second domain))
        ((or (eq domain :external-result) (external-value-domain-p build domain)) :unknown)
        ((and (consp domain) (eq (car domain) 'or))
         (reduce (lambda (left right) (merge-value-domains build left right))
                 (mapcar (lambda (part) (value-domain-shape build part)) (cdr domain))
                 :initial-value :pending))
        (t domain)))

(defun external-value-domain-p (build domain)
  "An unchanged value established by an actual installed-owner predicate.
The stable key names its owner obligation, never a class or slot type."
  (and (consp domain) (eq (car domain) :external-value)
       (snowgrave::source-finite-list-p domain) (= (length domain) 2)
       (assoc (second domain) (getf (build-declaration build) :external-value-guards) :test #'equal)))

(defun external-value-observation-p (build domain)
  (when (relational-value-domain-p domain)
    (return-from external-value-observation-p (external-value-observation-p build (third domain))))
  (or (external-value-domain-p build domain)
      (and (graph-node-domain-p domain) (external-value-observation-p build (third domain)))
      (and (consp domain) (eq (car domain) 'or)
           (some (lambda (part) (external-value-observation-p build part)) (cdr domain)))))

(defun external-result-type-p (build domain)
  (or (external-value-domain-p build domain)
      (native-value-type-p domain)
      (and (consp domain) (eq (car domain) 'or) (snowgrave::source-finite-list-p domain)
           (cdr domain) (every (lambda (part) (external-result-type-p build part)) (cdr domain)))))

(defun external-result-native-type (build domain)
  ;; The owner key is not a CL type. No THE assertion may invent a native
  ;; nominal class or stronger field declaration for an imported object.
  (cond ((external-value-domain-p build domain) t)
        ((and (consp domain) (eq (car domain) 'or))
         (cons 'or (mapcar (lambda (part) (external-result-native-type build part)) (cdr domain))))
        (t domain)))

(defun native-data-type-p (build domain)
  ;; Shared scalar/storage geometry test; provenance is checked by callers.
  (or (native-value-type-p domain)
      (and (not (member domain '(:unknown :pending :external-result)))
           (or (subtype-domain-p build domain 'number) (subtype-domain-p build domain 'symbol)
               (subtype-domain-p build domain 'string) (subtype-domain-p build domain 'character)))))

(defun native-data-domain-p (build domain)
  (when (relational-value-domain-p domain)
    (return-from native-data-domain-p (native-data-domain-p build (third domain))))
  (and (not (external-result-domain-p domain)) (not (owned-record-domain-p domain))
       (not (initializing-record-domain-p domain))
       (not (and (graph-state-profile-p build) (graph-private-container-domain-p build domain)))
       (or (and (graph-node-domain-p domain) (native-data-domain-p build (third domain)))
           (external-value-domain-p build domain)
           (and (consp domain) (eq (car domain) 'or)
                (every (lambda (part) (native-data-domain-p build part)) (cdr domain)))
           (and (consp domain) (eq (car domain) 'eql)
                (or (numberp (cadr domain)) (symbolp (cadr domain)) (characterp (cadr domain))))
           (native-data-type-p build domain))))

(defun native-data-form-p (build form)
  (cond ((and (consp form) (eq (car form) 'quote)) (serializable-tree-p (cadr form)))
        ((simple-vector-p form) (serializable-tree-p form))
        ((and (consp form) (member (car form) '(list list* cons)))
         (every (lambda (x) (native-data-form-p build x)) (cdr form)))
        (t (native-data-domain-p build (value-domain build form)))))

(defun native-sequence-form-p (build form)
  ;; LIST/VECTOR shape proof is distinct from native element-tree proof.
  ;; The general SEQUENCE superclass includes host extension methods.
  (subtype-domain-p build (value-domain build form) '(or list vector)))

(defun audit-external-call (build name arguments &key variable-tail)
  ;; Keeping an opaque host operation's function binding preserves its effects,
  ;; not its interpretation of a rewritten record or callable. The unchanged
  ;; boundary currently has a proof only for native scalar/readable data trees.
  ;; A record/callable/shared-layout ABI needs its actual external owner seam.
  (when (and (not *collect-function-flow*)
             (member-name name (getf (build-declaration build) :external-operations)))
    (when (graph-state-profile-p build)
      (audit-graph-native-inputs build arguments :graph-state-external-argument))
    ;; An owner guard has an explicit all-logical-values rejection ABI. It
    ;; must establish unchanged identity before interpreting the candidate;
    ;; its positive result, not argument syntax, is the import proof.
    (when (find name (getf (build-declaration build) :external-value-guards) :key #'second :test #'name=)
      (unless (and (not variable-tail) (= (length arguments) 1))
        (fail build 'snowgrave:unclosed-call :external-value-guard-arity
              "An installed-value guard takes exactly one candidate." :reachability))
      (return-from audit-external-call t))
    (let ((contract (assoc name (getf (build-declaration build) :external-argument-domains) :test #'name=)))
      (when contract
        (unless (and (not variable-tail) (= (length arguments) (length (second contract)))
                     (every (lambda (argument expected)
                              (subtype-domain-p build (value-domain build argument) expected))
                            arguments (second contract)))
          (fail build 'snowgrave:unclosed-call :external-argument-contract
                "This external result/state ABI requires its proved argument tuple at every call site." :reachability))))
    (unless (and (not variable-tail)
                 (every (lambda (argument) (native-data-form-p build argument)) arguments))
      (fail build 'snowgrave:unclosed-call :external-value-representation
            (format nil "External ~S needs native data argument proofs or an admitted logical record/callable ABI; an unchanged host binding cannot inspect rewritten values equivalently." name)
            :reachability))))

(defun external-shared-binding-p (build name local-specials)
  (and (not *collect-function-flow*)
       (or (getf (build-declaration build) :external-operations) (graph-state-profile-p build))
       (or (special-variable-p build name) (assoc name local-specials))))

(defun audit-external-shared-binding (build name compatiblep &optional local-specials)
  ;; Source specials retain their actual symbol identities. Publishing a
  ;; relocated callable into one changes an opaque zero-argument observer just
  ;; as surely as passing it directly. Use the existing value proof; do not
  ;; mistake a reproducible initializer for a representation-compatible one.
  (when (and (external-shared-binding-p build name local-specials) (not compatiblep))
    (fail build 'snowgrave:unclosed-call :external-shared-state-representation
          (format nil "Shared special ~S needs an admitted external state ABI before storing a rewritten or unproved value." name)
          :reachability)))

(defun audit-external-shared-value (build name value &optional local-specials (knownp t))
  (when (external-shared-binding-p build name local-specials)
    (audit-external-shared-binding build name (and knownp (native-data-form-p build value)) local-specials)))

(defun audit-external-place-value (build place value)
  (when (and (graph-state-profile-p build) (not *collect-function-flow*) (consp place))
    (if (eq (car place) 'slot-value)
        (progn (audit-graph-record-slot build (second place) (third place))
               (audit-stored-record-value build (second place) (third place) (value-domain build value)))
        (progn
         (audit-graph-native-inputs build (list value) :graph-state-write)
         (loop for argument in (cdr place) for position from 0
              unless (and (= position 0) (member (car place) '(aref svref car cdr nth))
                          (native-sequence-form-p build argument)
                          (not (graph-private-container-domain-p build (value-domain build argument))))
              do (audit-graph-native-inputs build (list argument) :graph-state-place)))))
  (when (and (not *collect-function-flow*)
             (or (build-classes build) (getf (build-declaration build) :closed-generics))
             (external-result-domain-p (value-domain build value))
             ;; An exact captured value already has this installation's
             ;; identity/custody. Its logical field store was type/slot-audited
             ;; above; this is not an ABI for an opaque external return.
             (not (and (graph-state-profile-p build) (consp place) (eq (first place) 'slot-value)
                       (graph-captured-identity-domain-p build (value-domain build value)))))
    (fail build 'snowgrave:unclosed-call :external-result-state
          "An unclassified external result cannot be retained in closed or shared state without its value ABI." :reachability))
  (cond ((symbolp place) (audit-external-shared-value build place value))
        ((and (not *collect-function-flow*)
              (getf (build-declaration build) :external-operations)
              (or (build-classes build)
                  (getf (build-declaration build) :closed-generics))
              ;; These places belong to the cohort's logical record ABI.
              ;; Ordinary aggregates may alias caller or shared host storage.
              (not (or (eq (car place) 'slot-value)
                       (member-name (list 'setf (car place))
                                    (getf (build-declaration build) :closed-generics))
                       (member-name (list 'setf (car place))
                                    (getf (build-declaration build) :external-operations))))
              (not (native-data-form-p build value))
              ;; AREF into proved scalar-valued native storage cannot publish
              ;; a rewritten object: a non-element value signals first. The
              ;; ordinary setter owns its bounds/type condition and logical
              ;; datum; no pre-emptive failure, copy or alternate writer runs.
              (not (and (consp place) (eq (car place) 'aref)
                        (standard-operation-meaning-p build 'aref)
                        (standard-operation-meaning-p build '(setf aref))
                        (let ((domain (value-domain build (second place))))
                          (and (native-value-type-p domain) (subtype-domain-p build domain 'array))))))
         (fail build 'snowgrave:unclosed-call :external-shared-state-representation
               "An ordinary aggregate write needs native value proof or an external alias/state ABI; private ownership cannot be assumed from place syntax."
               :reachability))))

(defun scalar-equality-tuple-p (build domains)
  ;; A rewritten record/callable cannot become a native number, symbol or
  ;; character. Comparing against one such operand needs no opaque alias
  ;; interpretation or recursive aggregate walk.
  (and (= (length domains) 2)
       (some (lambda (domain)
               (and (not (record-domain-p build domain))
                    (or (subtype-domain-p build domain 'number)
                        (subtype-domain-p build domain 'symbol)
                        (subtype-domain-p build domain 'character)))) domains)))

(defun audit-external-identity (build name arguments &key variable-tail)
  (when (and (not *collect-function-flow*) (member name '(eq eql equal equalp))
             (getf (build-declaration build) :external-operations))
    (let* ((domains (mapcar (lambda (argument) (value-domain build argument)) arguments))
           (cohort-callables
             (mapcar (lambda (argument)
                       (let ((targets (known-function-targets build argument)))
                         (and targets
                              (every (lambda (target)
                                       (or (member-name target (build-functions build))
                                           (member-name target (getf (build-declaration build) :closed-generics))))
                                     targets)))) arguments)))
      (when (and (or (build-classes build)
                     (getf (build-declaration build) :closed-generics)
                     (some #'identity cohort-callables))
                 (not (and (not variable-tail)
                           (or (every (lambda (argument) (native-data-form-p build argument)) arguments)
                               (scalar-equality-tuple-p build domains)
                               (every (lambda (domain) (record-domain-p build domain)) domains)
                               (and (member name '(eq eql))
                                    (every (lambda (domain) (graph-captured-identity-domain-p build domain)) domains))
                               (every #'identity cohort-callables)))))
        (fail build 'snowgrave:unclosed-call :external-logical-identity
              "Identity across an opaque external return or alias needs a logical value ABI; an original callable/record must not compare against its rewritten representative."
              :reachability)))))

(defun record-equality-realization (build arguments &key variable-tail)
  "Choose the same logical EQUALP semantics for direct and indirect calls."
  (when (and (not *collect-function-flow*) (build-classes build))
    (let ((domains (mapcar (lambda (argument) (value-domain build argument)) arguments)))
      (cond ((some (lambda (domain) (record-domain-p build domain)) domains) :identity)
            ((and (not variable-tail) (scalar-equality-tuple-p build domains)) :native)
            ((and (not variable-tail)
                  (every (lambda (argument) (native-data-form-p build argument)) arguments)) :native)
            (t (fail build 'snowgrave:unclosed-class-operation :recursive-record-equality
                     "EQUALP on an unproved aggregate needs identity-preserving closed-record equality lowering."))))))

(defun record-sequence-form-p (build form)
  "Prove every element of a fresh proper list is a closed record."
  (cond ((and (consp form) (eq (car form) 'list) (cdr form))
         (every (lambda (element) (record-domain-p build (value-domain build element))) (cdr form)))
        ((and (consp form) (eq (car form) 'progn))
         (record-sequence-form-p build (car (last (cdr form)))))
        ((and (consp form) (eq (car form) 'if))
         (and (record-sequence-form-p build (third form))
              (record-sequence-form-p build (fourth form))))))

(defun mapping-equality-realization (build name data variable-tail)
  ;; MAPLIST passes tails rather than elements; general reducers and keyword
  ;; predicates have different tuples. Do not apply the element proof to them.
  (when (and (not *collect-function-flow*) (not variable-tail)
             (member name '(mapcar mapc)) (= (length data) 2))
    (cond ((some (lambda (sequence) (record-sequence-form-p build sequence)) data) :identity)
          ((every (lambda (sequence) (native-data-form-p build sequence)) data) :native))))

(defun callback-required-count (build target)
  (cond ((local-function-binding-p target)
         (length (getf (lambda-contract build (second (local-function-binding-definition target))) :required)))
        ((and (consp target) (eq (first target) 'lambda))
         (length (getf (lambda-contract build (second target)) :required)))
        ((ordinary-function-form build target)
         (length (getf (lambda-contract build (third (ordinary-function-form build target))) :required)))
        ((member-name target (getf (build-declaration build) :closed-generics))
         (length (generic-domain-roots build target)))))

(defun literal-callback-return-summary (build lambda arity origin feedback-p)
  ;; Only this literal occurrence owns these definition-site captures. A
  ;; lexical variable containing an anonymous function has no such identity
  ;; proof and is rejected at the existing computed-callee boundary.
  (let (domains summary)
    (loop
      (audit-lambda-parser-inputs build (lambda-contract build (second lambda))
                                 (make-list arity :initial-element origin) nil :literal-callback)
      (setf domains (call-lambda-domains build (second lambda)
                                         (make-list arity :initial-element origin) nil :lexical t
                                         :specials (body-special-domains (cddr lambda)))
            summary (lambda-return-summary build (second lambda) domains (cddr lambda) :lexical t))
      (unless (and feedback-p (not (eq origin :external-result))
                   (external-result-domain-p (return-summary-primary summary)))
        (return))
      (setf origin :external-result))
    (let* ((old (assoc lambda *immediate-lambda-domains*))
           (merged (if old (mapcar (lambda (previous new) (merge-value-domains build previous new)) (cdr old) domains)
                       domains)))
      ;; Fresh alist cells leave enclosing capture identities untouched.
      (setf *immediate-lambda-domains*
            (acons lambda merged (remove lambda *immediate-lambda-domains* :key #'car))))
    summary))

(defun validate-callback (build reference arity local open
                          &key (data nil data-p) equalp-realization feedback-p)
  (multiple-value-bind (targets global-targets) (known-function-targets build reference)
    (let* ((literal (cond ((and (consp reference) (eq (car reference) 'function))
                          (function-expression-target reference))
                         ((and (consp reference) (eq (car reference) 'lambda)) reference)
                         ((and (consp reference) (eq (car reference) 'load-time-value)) (function-expression-target reference))
                         ((symbolp reference) (resolved-function build reference))))
           (names (or targets (when (and literal (not (eq literal :unknown))) (list literal))))
           (origin (if (or (some (lambda (input) (external-result-domain-p (value-domain build input))) data)
                           (and feedback-p
                                (some (lambda (name)
                                        (external-result-domain-p
                                         (return-summary-primary
                                          (cond ((local-function-binding-p name) (local-function-binding-summary name))
                                                ((and (consp name) (eq (first name) 'lambda)) nil)
                                                (t (source-call-return-summary build name global-targets)))))) names)))
                       :external-result :unknown))
           (arguments (loop repeat arity collect (gensym "CALLBACK-ARGUMENT")))
           (*argument-domains* (append (mapcar (lambda (argument) (cons argument origin)) arguments) *argument-domains*))
           (summary :pending))
      (when (special-variable-p build reference)
        (fail build 'snowgrave:unclosed-call :mutable-callback-special
              "The higher-order call cannot prove a mutable special's binding domain."))
      (unless (or open names *collect-function-flow*)
        (fail build 'snowgrave:unclosed-call :callback-target
              "A higher-order operation needs a checked capture or complete finite named callback domain."))
      (dolist (name names)
        (let* ((literal-lambda-p (and (consp name) (eq (first name) 'lambda)))
               (required (unless open (callback-required-count build name)))
               (unreachable-p (and required (< arity required)))
               (literal-summary nil))
        (unless (or open unreachable-p)
          (cond
            (literal-lambda-p
             (setf literal-summary (literal-callback-return-summary build name arity origin feedback-p)))
            ((local-function-binding-p name)
             (let* ((definition (local-function-binding-definition name))
                    (domains (call-in-local-function-environment
                              build (local-function-binding-frame name) t
                              (lambda ()
                                (audit-lambda-parser-inputs build (lambda-contract build (second definition))
                                                           (make-list arity :initial-element origin) nil
                                                           (local-function-binding-name name))
                                (call-lambda-domains build (second definition)
                                                     (make-list arity :initial-element origin) nil :lexical t
                                                     :specials (body-special-domains (cddr definition)))))))
               (record-local-function-inputs build name domains)))
            (t
             ;; Actual callback origins use the same lambda/GF caller owner
             ;; as an ordinary call. A FUNCTION capture alone says nothing
             ;; about elements returned by an imported sequence or KEY.
             (when (member-name name (getf (build-declaration build) :closed-generics))
               (let ((roots (generic-domain-roots build name)))
                 (unless (and (>= arity (length roots)) (every (lambda (axis) (member t axis)) roots))
                   (fail build 'snowgrave:incomplete-domain :callback-argument-domain
                         "A specialized higher-order callback needs sequence-element/reachability proof.")))
               (audit-generic-call build name arguments))
             (audit-function-call build name arguments)))
          (setf summary
                (merge-return-summaries
                 build summary
                 (or literal-summary
                     (if (local-function-binding-p name) (local-function-binding-summary name)
                         (source-call-return-summary build name global-targets))
                     (make-return-summary (list (if (eq origin :external-result) :external-result :unknown)) nil)))))
        (unless (or open unreachable-p literal-lambda-p (local-function-binding-p name)
                    (and (member-name name local) (not (member-name name global-targets))))
          (audit-external-identity build name data :variable-tail (not data-p))
          (when (and (not *collect-function-flow*)
                     (member-name name (getf (build-declaration build) :external-operations))
                     (not (and data-p (every (lambda (argument) (native-data-form-p build argument)) data))))
            (fail build 'snowgrave:unclosed-call :external-callback-representation
                  "An external callback needs native element/accumulator/keyword value proofs or an admitted logical ABI." :reachability))
          (when (and (not *collect-function-flow*) (eq name 'equalp) (build-classes build)
                     (not equalp-realization))
            (fail build 'snowgrave:unclosed-class-operation :equalp-callback
                  "Native EQUALP recursively observes lowered record structure; this callback needs an exact equality lowering."))
          (when (member name *representation-sensitive-ordinary-operations*)
            (audit-ordinary-operation build name data local open :variable-tail (not data-p))))))
      summary)))

(defun keyword-callback-key-data (build tail data local open)
  "Extend existing callback inputs with the first effective KEY return fact."
  (unless (and (snowgrave::source-finite-list-p tail) (evenp (length tail))
               (loop for rest on tail by #'cddr always (keywordp (first rest))))
    (fail build 'snowgrave:unclosed-call :callback-target
          "Callback keywords need literal names and a finite ordered argument shape."))
  (let ((reference (getf tail :key)))
    (if (or open (null reference)) (values data nil)
        (let* ((summary (validate-callback build reference 1 local open :data data))
               (variable (gensym "KEY-RESULT")))
          (values (append data (list variable))
                  (list (cons variable (return-summary-primary summary))))))))

(defun validate-keyword-callbacks (build tail local open &optional equalp-realization &key data)
  (unless (and (evenp (length tail))
               (loop for rest on tail by #'cddr always (keywordp (car rest))))
    (fail build 'snowgrave:unclosed-call :callback-target
          "Callback keywords need literal names and a complete ordered argument shape."))
  (when (and equalp-realization
             (loop for rest on tail by #'cddr thereis (eq (car rest) :test))
             (loop for rest on tail by #'cddr thereis (eq (car rest) :test-not)))
    (fail build 'snowgrave:unclosed-call :conflicting-equality-tests
          "Simultaneous TEST and TEST-NOT need the ordinary operator's exact error contract."))
  (multiple-value-bind (key-data domains) (keyword-callback-key-data build tail data local open)
   (let ((*argument-domains* (append domains *argument-domains*)))
    (loop with seen = nil
        for rest on tail by #'cddr for index from 1 by 2
        when (member (car rest) '(:test :test-not :key))
          do (unless (and (eq (car rest) :key) (null (cadr rest)))
               (validate-callback build (cadr rest) (if (eq (car rest) :key) 1 2) local open
                                  :data (if (eq (car rest) :key) data key-data)
                                  :equalp-realization (and (not (eq (car rest) :key)) equalp-realization)))
        when (and (not (member (car rest) seen))
                  (member (car rest) '(:test :test-not))
                  (eq equalp-realization :identity)
                  (member 'equalp (known-function-targets build (cadr rest))))
          collect index
        when (member (car rest) '(:test :test-not))
          do (pushnew (car rest) seen)))))

(defun coerce-sequence-target-p (type)
  "Finite built-in sequence type syntax, without user DEFTYPE or MOP queries."
  (labels ((sizep (size) (or (eq size '*) (and (integerp size) (<= 0 size))))
           (elementp (element) (or (member element '(t * bit)) (native-value-type-p element))))
    (or (member type '(list vector simple-vector string simple-string base-string
                      simple-base-string bit-vector simple-bit-vector))
        (and (snowgrave::source-finite-list-p type)
             (case (car type)
               (vector (and (member (length type) '(2 3)) (elementp (second type))
                            (or (= (length type) 2) (sizep (third type)))))
               ((array simple-array)
                (and (= (length type) 3) (elementp (second type))
                     (snowgrave::source-finite-list-p (third type))
                     (= (length (third type)) 1) (sizep (first (third type)))))
               ((simple-vector string simple-string base-string simple-base-string
                 bit-vector simple-bit-vector)
                (and (= (length type) 2) (sizep (second type)))))))))

(defun coerce-result-domain (build arguments)
  ;; Copying an ordinary sequence preserves its elements, including logical
  ;; records. It does not classify an opaque external aggregate's contents.
  (let ((input (value-domain build (first arguments))))
    (multiple-value-bind (target constantp) (quoted-value (second arguments))
      (values (qualify-domain-origin
               (if (and constantp (coerce-sequence-target-p target)) target :unknown) input)
              t))))

(defun native-sequence-result-domain (build input)
  ;; Sequence shape says nothing about element representation. Filtering may
  ;; turn a CONS into NIL; retain only the sequence family, and opaque origin.
  (let ((domain (value-domain build input)))
    (if (eq domain :pending) :pending
        (qualify-domain-origin
         (cond ((subtype-domain-p build domain 'list) 'list)
               ((subtype-domain-p build domain 'string) 'string)
               ((subtype-domain-p build domain 'vector) 'vector)
               ((subtype-domain-p build domain '(or list vector)) '(or list vector))
               (t :unknown))
         domain))))

(defun ordinary-call-argument-plan (build form &key required-count)
  "Use the existing ordered producer owner for every MVC tuple."
  (case (car form)
    (funcall (values (cddr form) nil t))
    (apply
     (let ((tail (car (last form))))
       (cond ((null tail) (values (butlast (cddr form)) nil t))
             ((and (consp tail) (eq (car tail) 'list))
              (values (append (butlast (cddr form)) (cdr tail)) nil t))
             ((and (consp tail) (eq (car tail) 'quote)
                   (snowgrave::source-finite-list-p (second tail)))
              (values (append (butlast (cddr form))
                              (mapcar (lambda (value) (list 'quote value)) (second tail))) nil t))
             ((and required-count (>= (length (butlast (cddr form))) required-count))
              (values (butlast (cddr form)) nil t
                      (if (external-result-domain-p (value-domain build tail)) :external-result t))))))
    (multiple-value-call
     (multiple-value-bind (arguments bindings domains completep pendingp)
         (multiple-value-call-plan build (cddr form) :literal-proofs nil)
       (declare (ignore bindings))
       (values arguments domains completep nil pendingp)))))

(defun native-sequence-argument-position (name)
  (case name ((coerce length fill reverse) 0) ((remove delete) 1)))

(defun asserted-sequence-expression (build source expression)
  ;; Export only already proved LIST/VECTOR geometry to the host compiler.
  ;; COERCE/LENGTH/FILL audit it as an admission requirement; sequence-family
  ;; operations may use it when available without assuming an unproved shape.
  (let* ((domain (value-domain build source))
         (shape (cond ((subtype-domain-p build domain 'list) 'list)
                      ((subtype-domain-p build domain 'vector) 'vector)
                      ((subtype-domain-p build domain '(or list vector)) '(or list vector)))))
    (if shape `(the ,shape ,expression) expression)))

(defun asserted-sequence-arguments (build sources arguments position)
  ;; APPLY retains a final tail form even when its flattened source tuple has
  ;; no additional values. Never truncate the emitted invocation to that tuple.
  (loop for argument in arguments for index from 0
        collect (if (and (= index position) (< position (length sources)))
                    (asserted-sequence-expression build (nth position sources) argument) argument)))

(defun native-sequence-indirect-arguments (build form transformed position)
  "Annotate the actual receiver once, preserving call/value producer order."
  (multiple-value-bind (arguments domains completep) (ordinary-call-argument-plan build form)
    (if (or (not completep) (>= position (length arguments))) transformed
        (let ((source (nth position arguments)) (*argument-domains* (append domains *argument-domains*)))
          (case (car form)
            (funcall (asserted-sequence-arguments build arguments transformed position))
            (apply
             (let ((prefix (1- (length transformed))))
               (if (< position prefix)
                   (asserted-sequence-arguments build arguments transformed position)
                   (let ((tail (car (last transformed))))
                     (if (and (consp tail) (eq (car tail) 'list))
                         (append (butlast transformed)
                                 (list (cons 'list (asserted-sequence-arguments
                                                    build (nthcdr prefix arguments) (cdr tail) (- position prefix)))))
                         transformed)))))
            (multiple-value-call
             (let ((offset 0))
               (mapcar (lambda (producer)
                         (let* ((count (length (cdr producer)))
                                (annotated
                                  (if (<= offset position (+ offset count -1))
                                      (cons 'values
                                            (loop for argument in (cdr producer) for index from offset
                                                  collect (if (= index position)
                                                              (asserted-sequence-expression build source argument) argument)))
                                      producer)))
                           (incf offset count) annotated)) transformed)))
            (otherwise transformed))))))

(defun ordinary-scalar-result-domain (build name &optional global-targets)
  ;; Facts about successful standard calls, not argument assertions or a way
  ;; to skip their source/callback/residual audits. LENGTH's native receiver
  ;; proof belongs to audit-ordinary-operation.
  (let ((domain (case name ((ash logand logior logxor lognot) 'integer)
                           ((plusp eq eql equal equalp) 'boolean) (make-symbol 'symbol) (length '(integer 0 *)))))
    (when (and domain (standard-operation-meaning-p build name nil global-targets)) domain)))

(defun ordinary-single-value-result-p (build name &optional global-targets)
  ;; Only normal-return cardinality, never permission to omit operation,
  ;; callback, argument, representation or residual audits. In particular a
  ;; reducer can forward its callback's values, so REDUCE is not in this list.
  (and (or (ordinary-scalar-result-domain build name global-targets)
           (member name '(eq eql equal equalp identity not null atom consp symbolp
                          numberp integerp rationalp floatp realp complexp stringp
                          characterp vectorp arrayp keywordp
                          fill coerce mapc mapl reverse nreverse remove delete
                          list list* cons vector mapcar maplist mapcan)))
       (standard-operation-meaning-p build name nil global-targets)))

(defun ordinary-indirect-result-domain (build form targets global-targets)
  (when (member (car form) '(funcall apply multiple-value-call))
    (when (and targets
               (every (lambda (target)
                        (or (and (member target '(fill coerce mapc reverse remove delete mapcar maplist mapcan reduce))
                                 (standard-operation-meaning-p build target nil global-targets))
                            (ordinary-scalar-result-domain build target global-targets))) targets))
      (multiple-value-bind (arguments domains completep) (ordinary-call-argument-plan build form)
        (when completep
          (let ((*argument-domains* (append domains *argument-domains*)))
            (values (reduce (lambda (old target)
                             (merge-value-domains build old
                               (case target
                                 (coerce (coerce-result-domain build arguments))
                                 (fill (value-domain build (first arguments)))
                                 (mapc (value-domain build (second arguments)))
                                 (reverse (native-sequence-result-domain build (first arguments)))
                                 ((remove delete) (native-sequence-result-domain build (second arguments)))
                                 ((mapcar maplist mapcan reduce) (callback-operator-result-domain build target arguments))
                                 (otherwise (ordinary-scalar-result-domain build target global-targets)))))
                           targets :initial-value :pending) t)))))))

(defun callback-operator-result-domain (build name arguments)
  "Compose callback results through the existing return and input fixed point."
  (let* ((reference (first arguments))
         (data (rest arguments))
         (arity (if (eq name 'reduce) 2 (length data))))
    (multiple-value-bind (callback-data domains)
        (if (eq name 'reduce)
            (keyword-callback-key-data build (cddr arguments) data *value-domain-local-functions* nil)
            (values data nil))
      (let* ((*argument-domains* (append domains *argument-domains*))
             ;; A result query consumes the same logical callback contract as
             ;; emission. EQUALP on closed record elements is admitted only
             ;; when the existing mapping owner proves its exact realization.
             (realization (and (member 'equalp (known-function-targets build reference))
                               (mapping-equality-realization build name data nil)))
             (summary (validate-callback build reference arity *value-domain-local-functions* nil
                                         :data callback-data :equalp-realization realization
                                         :feedback-p (eq name 'reduce))))
        (when (and (eq name 'reduce)
                   (not (loop for tail on (cddr arguments) by #'cddr thereis (eq (first tail) :initial-value))))
          (setf summary (merge-return-summaries
                         build summary
                         (validate-callback build reference 0 *value-domain-local-functions* nil
                                            :data callback-data :feedback-p t))))
        (let ((returned (return-summary-primary summary)))
          (values
           (cond
             ;; REDUCE can also return an untouched initial value or a single
             ;; keyed element. An imported origin on any such edge survives.
             ((or (external-result-domain-p returned)
                  (and (eq name 'reduce)
                       (some (lambda (input) (external-result-domain-p (value-domain build input))) callback-data)))
              :external-result)
             ((eq returned :pending) :pending)
             ((member name '(mapcar maplist)) 'list)
             ;; MAPCAN's final NCONC argument can itself be an arbitrary
             ;; object; do not invent proper-list shape from its operator.
             ((eq name 'mapcan) (merge-value-domains build 'list returned))
             (t :unknown))
           t))))))

(defun audit-ordinary-operation (build name arguments local open &key variable-tail)
  "Apply one logical observation/callback policy to direct and indirect calls."
  (let ((equality-positions nil))
  (unless (member-name name local)
    (unless open (audit-graph-ordinary-inputs build name arguments))
    (when (eq name 'coerce)
      (unless (and (not variable-tail) (= (length arguments) 2))
        (fail build 'snowgrave:unclosed-call :coerce-arguments
              "COERCE needs a complete object/target tuple."))
      (multiple-value-bind (type constantp) (quoted-value (second arguments))
        (unless (and constantp (coerce-sequence-target-p type))
          (fail build 'snowgrave:unclosed-call :coerce-target
                "COERCE admits only literal built-in sequence targets; FUNCTION, dynamic types and user type expanders need separate closure.")))
      (unless (or open *collect-function-flow* (native-sequence-form-p build (first arguments)))
        (fail build 'snowgrave:unclosed-call :coerce-sequence-domain
              "COERCE needs an ordinary LIST/VECTOR input proof; extended sequence methods are not an intrinsic.")))
    (when (and (eq name 'length) (not open))
      (unless (and (not variable-tail) (= (length arguments) 1))
        (fail build 'snowgrave:unclosed-call :length-arguments
              "LENGTH needs a complete one-argument tuple."))
      (unless (or *collect-function-flow* (native-sequence-form-p build (first arguments)))
        (fail build 'snowgrave:unclosed-call :length-sequence-domain
              "LENGTH needs an ordinary LIST/VECTOR input proof; extended sequence methods are not an intrinsic.")))
    (when (and (eq name 'fill) (not open))
      ;; FILL is an ordinary aggregate write with the same alias/state
      ;; obligation as its element setter. This synthetic place is proof
      ;; input only; the host FILL retains all actual evaluation, bounds,
      ;; keyword, mutation and result-identity semantics.
      (unless (>= (length arguments) 2)
        (fail build 'snowgrave:unclosed-call :fill-arguments
              "FILL needs a proved sequence/value prefix before its write can be audited."))
      (audit-external-place-value build `(aref ,(first arguments) 0) (second arguments))
      (unless (or *collect-function-flow* (native-sequence-form-p build (first arguments)))
        (fail build 'snowgrave:unclosed-call :fill-sequence-domain
              "FILL needs a proved ordinary list/vector receiver; host sequence extension methods are not implicit dependencies.")))
    (when (and (not open) (member name '(gethash remhash)))
      (when (and variable-tail (build-classes build) (< (length arguments) 2))
        (fail build 'snowgrave:unclosed-class-operation :record-hash-table-domain
              "A variable hash-access tail needs a proven complete key/table tuple."))
      (validate-hash-access build (first arguments) (second arguments)))
    (when (eq name 'make-hash-table)
      (unless (and (not variable-tail) (evenp (length arguments))
                   (loop for tail on arguments by #'cddr always (keywordp (car tail))))
        (fail build 'snowgrave:unclosed-call :hash-table-test
              "Hash construction needs literal keyword names and a complete equality-test contract."))
      (let ((test (getf arguments :test ''eql)))
        (multiple-value-bind (test-name quotedp) (quoted-value test)
          (unless (and quotedp (member test-name '(eq eql equal equalp)))
            (fail build 'snowgrave:unclosed-call :hash-table-test
                  "Only explicit standard hash-table equality tests have a closed contract."))
          (when (and (eq test-name 'equalp) (build-classes build))
            (fail build 'snowgrave:unclosed-class-operation :equalp-hash-table
                  "An EQUALP hash table needs identity-preserving closed-record equality/hash realization.")))))
    (when (member name '(mapcar mapc maplist mapcan reduce remove-if delete-if sort stable-sort))
      (let ((reference (if (member name '(sort stable-sort)) (second arguments) (first arguments)))
            (arity (cond ((member name '(mapcar mapc maplist mapcan)) (length (cdr arguments)))
                         ((member name '(remove-if delete-if)) 1) (t 2)))
            (data (if (member name '(sort stable-sort))
                      (cons (first arguments) (cddr arguments)) (cdr arguments))))
        ;; A known prefix cannot prove omitted sequences/elements native. The
        ;; count is only the proved lower bound; do not forge a full data tuple.
        (multiple-value-bind (callback-data domains)
            (if (and (not variable-tail) (member name '(reduce remove-if delete-if sort stable-sort)))
                (keyword-callback-key-data build (cddr arguments) data local open)
                (values data nil))
          (let ((*argument-domains* (append domains *argument-domains*))
                (realization (and (not open)
                                  (member 'equalp (known-function-targets build reference))
                                  (mapping-equality-realization build name data variable-tail))))
            (if variable-tail (validate-callback build reference arity local open)
                (validate-callback build reference arity local open :data callback-data :equalp-realization realization
                                   :feedback-p (eq name 'reduce)))
            (when (and (eq name 'reduce) (not variable-tail)
                       (not (loop for tail on (cddr arguments) by #'cddr thereis (eq (first tail) :initial-value))))
              (validate-callback build reference 0 local open :data callback-data :feedback-p t))
            (when (eq realization :identity) (push 0 equality-positions))))))
    (when (member name '(member assoc find position count remove delete remove-if delete-if reduce sort stable-sort))
      ;; These calls can carry a callback in an omitted keyword tail. Ordinary
      ;; positional syntax must not be mistaken for proof of that tail's ABI.
      (when (and variable-tail (not *collect-function-flow*))
        (fail build 'snowgrave:unclosed-call :callback-target
              "A variable keyword tail needs exact callback/element contracts."))
      (let ((realization
              (when (and (not open) (not *collect-function-flow*) (not variable-tail)
                         (member name '(member assoc find position count remove delete)))
                (cond ((record-domain-p build (value-domain build (first arguments)))
                       (unless (subtype-domain-p build (value-domain build (second arguments))
                                                 (if (member name '(member assoc)) 'list 'sequence))
                         (fail build 'snowgrave:unclosed-call :callback-sequence-domain
                               "A lowered search item needs a proven ordinary sequence receiver, separate from element identity."))
                       :identity)
                      ((and (>= (length arguments) 2)
                            (native-data-form-p build (first arguments))
                            (native-data-form-p build (second arguments))
                            (not (loop for rest on (cddr arguments) by #'cddr
                                       thereis (and (eq (car rest) :key) (cadr rest))))) :native)))))
        (setf equality-positions
              (append equality-positions
                      (mapcar (lambda (index) (+ 2 index))
                              (validate-keyword-callbacks build (cddr arguments) local open realization
                                                          :data (if (member name '(sort stable-sort)) (list (first arguments))
                                                                    (if (member name '(remove-if delete-if reduce))
                                                                        (list (second arguments)) (subseq arguments 0 (min 2 (length arguments)))))))))))
    (when (and (not open) (not *collect-function-flow*) (member name '(format princ prin1 print)))
      (unless (and (not variable-tail)
                   (every (lambda (argument) (native-data-form-p build argument))
                          (if (eq name 'format) (cddr arguments) (list (first arguments)))))
        (fail build 'snowgrave:unclosed-class-operation :printed-record-or-metaobject
              "Printing requires a proven native data tree or an exact record/metaobject print mapping."))))
  equality-positions))

(defun validate-record-slot (build record-form slot)
  (when *collect-function-flow* (return-from validate-record-slot (build-layouts build)))
  (let* ((domain (value-domain build record-form))
         (layouts (remove-if-not (lambda (layout)
                                   (some (lambda (actual) (subtype-domain-p build (getf layout :class) (private-record-domain-base actual)))
                                         (domain-alternatives domain))) (build-layouts build))))
    (unless (and (record-domain-p build domain) layouts
                 (symbolp slot) (symbol-package slot))
      (fail build 'snowgrave:unclosed-class-operation :record-slot-domain
            "A slot receiver needs an admitted sealed class and a stable constant slot name."))
    layouts))

(defun audit-missing-slot-writer (build place value)
  (when *collect-function-flow* (return-from audit-missing-slot-writer t))
  (when (and (consp place) (eq (car place) 'slot-value))
    (multiple-value-bind (slot constantp) (quoted-value (caddr place))
      (when (and constantp
                 (some (lambda (layout) (not (member slot (getf layout :slots))))
                       (validate-record-slot build (cadr place) slot))
                 (not (native-data-form-p build value)))
        (fail build 'snowgrave:unclosed-class-operation :missing-slot-writer-value
              "A missing-slot writer prints its value; lowered records or unknown values require an exact printer mapping.")))))

(defun validate-hash-access (build key table)
  (when *collect-function-flow* (return-from validate-hash-access t))
  (when (and (build-classes build) (not (native-data-form-p build key)))
    (unless (and (consp table) (eq (car table) 'make-hash-table)
                 (multiple-value-bind (test constantp) (quoted-value (getf (cdr table) :test ''eql))
                   (and constantp (member test '(eq eql equal)))))
      (fail build 'snowgrave:unclosed-class-operation :record-hash-table-domain
            "A record key requires a proven EQ/EQL/EQUAL table; an unknown table may expose structural EQUALP equality."))))

(defun captured-function (build variable)
  (let* ((definition (snowgrave:find-authored-definition (build-source build) :global variable))
         (form (and definition (normalized-definition-form build definition))))
    (when form
      (let ((initializer (caddr form)))
        (when (and (consp initializer) (eq (car initializer) 'load-time-value))
          (setf initializer (cadr initializer)))
        (when (and (consp initializer) (eq (car initializer) 'function))
          (cadr initializer))))))

(defun resolved-function (build variable)
  (if (special-variable-p build variable) :unknown
      (let ((binding (assoc variable *function-bindings*)))
        (or (and binding (not (eq (cdr binding) :unknown)) (cdr binding))
            (domain-function-target (binding-value-domain variable))
            (if binding :unknown (captured-function build variable))))))

(defun domain-function-target (domain)
  (when (and (consp domain) (eq (car domain) :function-target)) (second domain)))

(defun known-function-target (build form)
  "Syntax/binding fallback only; this result never proves a global owner."
  (cond ((symbolp form) (resolved-function build form))
        ((and (consp form) (eq (car form) 'lambda)) form)
        ((and (consp form) (eq (car form) 'function))
         (if (and (consp (second form)) (eq (caadr form) 'lambda)) (second form)
             (function-expression-target form)))
        ((and (consp form) (eq (car form) 'load-time-value))
         (let ((*argument-domains* nil) (*function-bindings* nil)
               (*declared-specials* nil) (*value-domain-local-functions* nil) (*local-function-frames* nil)
               (*immediate-lambda-domains* nil))
           (known-function-target build (second form))))
        (t :unknown)))

(defun immediate-lambda-form (build call)
  (declare (ignore build))
  ;; Only this syntactic occurrence owns the lambda's definition environment.
  ;; A separately saved anonymous closure has no such capture proof.
  (when (member (car call) '(funcall apply multiple-value-call))
    (let ((callee (second call)))
      (when (and (consp callee) (eq (car callee) 'function)) (setf callee (second callee)))
      (when (and (consp callee) (eq (car callee) 'lambda)) callee))))

(defun immediate-lambda-call-domains (build call)
  "Project the actual call tuple through the existing lambda binding owner."
  (let* ((lambda (immediate-lambda-form build call))
         (contract (lambda-contract build (second lambda))))
    (multiple-value-bind (arguments bindings completep variable-tail)
        (ordinary-call-argument-plan build call :required-count (length (getf contract :required)))
      (unless completep
        (unless *collect-function-flow*
          (fail build 'snowgrave:incomplete-domain :immediate-lambda-arguments
                "A literal lambda call needs a complete producer tuple or a proved APPLY prefix." :reachability))
        (return-from immediate-lambda-call-domains (values nil nil)))
      (let* ((*argument-domains* (append bindings *argument-domains*))
             (supplied (mapcar (lambda (argument) (value-domain build argument)) arguments)))
        (audit-lambda-parser-inputs build contract supplied variable-tail :literal-lambda)
        (values (call-lambda-domains
                 build (second lambda)
                 supplied
                 variable-tail :lexical t :specials (body-special-domains (cddr lambda)))
                t)))))

(defun immediate-lambda-return-summary (build call)
  (multiple-value-bind (domains completep) (immediate-lambda-call-domains build call)
    (if completep
        (let ((lambda (immediate-lambda-form build call)))
          (lambda-return-summary build (second lambda) domains (cddr lambda) :lexical t))
        :pending)))

(defun known-function-targets (build form)
  "Return finite targets, qualified global targets, and the one analysed domain.
A literal lexical FUNCTION may name a target without proving a global owner."
  (let* ((domain (value-domain build form))
         (alternatives (domain-alternatives domain)))
    (if (every #'domain-function-target alternatives)
        (let ((targets (remove-duplicates (mapcar #'domain-function-target alternatives) :test #'name=)))
          (values targets targets domain))
        (let ((target (known-function-target build form)))
          (values (when (and target (not (eq target :unknown))) (list target)) nil domain)))))

(defun function-expression-target (form)
  (when (and *cold-recipe-source-marker* (consp form) (eq (car form) *cold-recipe-source-marker*))
    (return-from function-expression-target (function-expression-target (second form))))
  (cond ((and (consp form) (eq (car form) 'load-time-value))
         (let ((*local-function-frames* nil)) (function-expression-target (second form))))
        ((and (consp form) (eq (car form) 'function))
         (if (and (consp (second form)) (eq (caadr form) 'lambda)) :unknown
             (or (find-local-function-binding (second form)) (second form))))
        (t :unknown)))

(defun analyze-let-scope (build bindings sequential-p process &key open specials)
  ;; The portable owner controls initializer order. Every adapter analysis
  ;; must extend both type and callable facts at the same lexical boundary.
  ;; Keeping only types leaves an outer callable proof live after shadowing.
  (let ((active-specials nil))
   (snowgrave:analyze-source-bindings
   bindings sequential-p (cons (copy-tree *argument-domains*) (copy-list *function-bindings*))
   (lambda (name initializer scope)
     (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope))
           (*declared-specials* (append (when sequential-p active-specials) *declared-specials*)))
       (unless open (audit-external-shared-value build name initializer specials))
       (multiple-value-bind (code receipt) (funcall process initializer)
         (values (list (if receipt (return-summary-primary receipt) (value-domain build initializer))
                       (function-expression-target initializer)
                       (or (native-data-form-p build initializer)
                           (graph-native-payload-form-p build initializer))) code))))
   (lambda (name fact scope)
     (let ((specialp (or (assoc name specials) (special-variable-p build name))))
       (when specialp (pushnew name active-specials))
       (let ((functions (acons name (if specialp :unknown (second fact)) (cdr scope))))
         (unless specialp
           (push (list name (assoc name functions) (first fact) (third fact) :initial)
                 *mutable-invariant-bindings*))
         (cons (acons name (if specialp :unknown (first fact)) (car scope)) functions))))
   :source-key (build-source-key build) :path (list (build-identity build)))))

(defun source-mutations (forms)
  "Collect conservative writes without using stale value/callable facts.
Nested scopes may add extra obligations for a same-named outer binding, but
can never hide a captured write or a write reached by a backedge."
  (let ((result nil))
    (labels ((write-to (place value)
               (when (symbolp place) (push (cons place value) result)))
             (walk (form)
               (when (consp form)
                 (case (car form)
                   ((quote declare) nil)
                   ((setq setf)
                    (loop for (place value) on (cdr form) by #'cddr do
                      (write-to place value) (unless (symbolp place) (walk place)) (walk value)))
                   ((incf decf)
                    (write-to (second form) (list (if (eq (car form) 'incf) '+ '-)
                                                 (second form) (if (cddr form) (third form) 1)))
                    (mapc #'walk (cddr form)))
                   ((push pushnew) (write-to (third form) (list 'cons (second form) (third form)))
                    (mapc #'walk (cdr form)))
                   (pop (write-to (second form) (list 'cdr (second form))))
                   (multiple-value-setq
                    (dolist (variable (second form)) (write-to variable :unknown))
                    (walk (third form)))
                   (function (when (and (consp (second form)) (eq (caadr form) 'lambda))
                               (walk (second form))))
                   (otherwise (mapc #'walk form))))))
      (mapc #'walk forms))
    result))

(defun numeric-declaration-type-p (type)
  ;; Do not invoke an arbitrary user DEFTYPE/SATISFIES expander while proving
  ;; an invariant. LOOP's ordinary numeric declarations include intersections.
  (and (or (native-value-type-p type)
           (and (consp type) (eq (car type) 'and) (cdr type)
                (every #'numeric-declaration-type-p (cdr type))))
       (subtypep type 'number)))

(defun body-numeric-declarations (body)
  (multiple-value-bind (prefix executable) (snowgrave::source-body-parts body)
    (declare (ignore executable))
    (loop for form in prefix when (and (consp form) (eq (car form) 'declare))
          append (loop for declaration in (cdr form)
                       for type = (if (eq (car declaration) 'type) (second declaration) (car declaration))
                       for names = (if (eq (car declaration) 'type) (cddr declaration) (cdr declaration))
                       when (numeric-declaration-type-p type) append (copy-list names)))))

(defun mutable-binding-fact (name)
  (let ((binding (assoc name *function-bindings*)))
    (find-if (lambda (fact) (and (eq name (first fact)) (eq binding (second fact))
                                 (not (eq (fifth fact) :initial))))
             *mutable-invariant-bindings*)))

(defun binding-native-payload-p (name)
  (let ((binding (assoc name *function-bindings*)))
    (fourth (find-if (lambda (fact) (and (eq name (first fact)) (eq binding (second fact))))
                     *mutable-invariant-bindings*))))

(defun binding-value-domain (name)
  ;; Predicate refinement cannot restore an initial or path-local fact across
  ;; an admitted write. Only the proved broad invariant survives for this
  ;; exact binding; a shadowing binder gets an independent fact.
  (let ((mutable (mutable-binding-fact name)))
    (if mutable (third mutable) (or (cdr (assoc name *argument-domains*)) :unknown))))

(defun source-body-flow-facts (build body)
  "Invalidate assigned lexical value/callee facts before every body analysis.
NUMBER/LIST are optional precision improvements, proved jointly against all
writes under widened bindings. Shape failure widens to UNKNOWN while opaque
origin always survives; this analysis never rejects SETQ by itself. Existing consumers still demand their own representation/call proof."
  (let* ((specials (body-special-domains body))
         (domains (append specials (copy-tree *argument-domains*)))
         (functions (append specials (copy-list *function-bindings*)))
         (writes (source-mutations body))
         (numeric (body-numeric-declarations body))
         (invariants (copy-list *mutable-invariant-bindings*))
         (candidates nil))
    (dolist (name (remove-duplicates (mapcar #'car writes)))
      (let ((fact (assoc name domains)))
        (when (and fact (not (or (assoc name specials) (special-variable-p build name))))
          (let* ((previous (binding-value-domain name))
                 (domain (cond ((external-result-domain-p previous) :external-result)
                               ((or (member name numeric) (subtype-domain-p build previous 'number)) 'number)
                               ((subtype-domain-p build previous 'list) 'list)
                               (t :unknown)))
                 (binding (assoc name functions)))
            ;; Do not mutate a captured outer alist cell. Keeping already
            ;; unknown binding-cons identity preserves enclosing invariants.
            (unless (and binding (eq (cdr binding) :unknown))
              (setf functions (acons name :unknown (remove name functions :key #'car)))
              (setf binding (assoc name functions)))
            (setf (cdr fact) domain)
            ;; Custody is independent of shape: POP can lose LIST geometry
            ;; while retaining the initial native payload guarantee.
            (let ((candidate (list name binding domain
                                   (or (binding-native-payload-p name)
                                       (not (graph-private-payload-domain-p build previous))))))
              (push candidate candidates) (push candidate invariants))))))
    (let ((*argument-domains* domains) (*function-bindings* functions)
          (*mutable-invariant-bindings* invariants))
      ;; Native shape can widen to UNKNOWN, then to a may-opaque envelope.
      ;; Recheck every dependency after either widening; opacity never falls
      ;; back to UNKNOWN merely because its shape invariant failed.
      (loop with changed = nil do
        (setf changed nil)
        (dolist (candidate candidates)
          (let* ((old (third candidate))
                 (inputs (loop for write in writes when (eq (car write) (first candidate))
                               collect (value-domain build (cdr write))))
                 (nativep (and (fourth candidate)
                               (loop for write in writes
                                     always (or (not (eq (car write) (first candidate)))
                                                (graph-native-payload-form-p build (cdr write))))))
                 (domain (cond ((or (external-result-domain-p old) (some #'external-result-domain-p inputs))
                                :external-result)
                               ((or (eq old :unknown)
                                    (not (every (lambda (input) (subtype-domain-p build input old)) inputs)))
                                :unknown)
                               (t old))))
            (unless (and (equal old domain) (eql (fourth candidate) nativep))
              (setf (third candidate) domain
                    (fourth candidate) nativep
                    (cdr (assoc (first candidate) domains)) domain
                    changed t))))
        (unless changed (return))))
    (values domains functions invariants (mapcar #'car specials))))

(defmacro with-source-body-facts ((body) &body code)
  (let ((domains (gensym "BODY-DOMAINS")) (functions (gensym "BODY-FUNCTIONS"))
        (invariants (gensym "BODY-INVARIANTS")) (specials (gensym "BODY-SPECIALS")))
    `(multiple-value-bind (,domains ,functions ,invariants ,specials)
         (source-body-flow-facts build ,body)
       (let ((*argument-domains* ,domains) (*function-bindings* ,functions)
             (*mutable-invariant-bindings* ,invariants)
             (*declared-specials* (append ,specials *declared-specials*)))
         ,@code))))

(defun admitted-mutation-p (name)
  (not (null (mutable-binding-fact name))))

(defstruct (return-summary (:constructor make-return-summary (domains completep &optional (effects :unowned))))
  domains completep effects)

(defun return-summary-primary (summary)
  (if (return-summary-p summary)
      (if (return-summary-domains summary) (car (return-summary-domains summary)) '(eql nil))
      summary))

(defun same-return-summary-p (a b)
  (or (eq a b)
      (and (return-summary-p a) (return-summary-p b)
           (eq (return-summary-completep a) (return-summary-completep b))
           (equal (return-summary-domains a) (return-summary-domains b))
           (equal (return-summary-effects a) (return-summary-effects b)))))

(defun merge-return-summaries (build previous additional)
  (cond ((eq previous :pending) additional)
        ((eq additional :pending) previous)
        (t
         (let ((old (return-summary-domains previous)) (new (return-summary-domains additional))
               (old-complete-p (return-summary-completep previous))
               (new-complete-p (return-summary-completep additional)))
           (make-return-summary
            (loop repeat (max (length old) (length new))
                  for old-tail = old then (cdr old-tail) for new-tail = new then (cdr new-tail)
                  collect (merge-value-domains
                           build (cond (old-tail (car old-tail)) (old-complete-p '(eql nil)) (t :unknown))
                                 (cond (new-tail (car new-tail)) (new-complete-p '(eql nil)) (t :unknown))))
            (and old-complete-p new-complete-p (= (length old) (length new)))
            (merge-record-flow-effects build (return-summary-effects previous)
                                       (return-summary-effects additional)))))))

(defun body-return-summary (build body)
  (with-source-body-facts (body)
    (form-return-summary build (car (last (remove-if (lambda (form)
                                                     (and (consp form) (eq (car form) 'declare))) body))))))

(defun ordinary-return-summary (build body)
  (multiple-value-bind (prefix executable) (split-source-body body)
    (with-source-body-facts (prefix)
      (reduce (lambda (old new) (merge-return-summaries build old new))
              (source-return-domains build executable #'form-return-summary)
              :initial-value (body-return-summary build executable)))))

(defun lambda-return-summary (build lambda-list domains body &key method lexical)
  ;; Methods and ordinary helpers share the same binding/escape analysis.
  (let ((*argument-domains* (when lexical *argument-domains*))
        (*function-bindings* (when lexical *function-bindings*))
        (*value-domain-local-functions* (when lexical *value-domain-local-functions*))
        (*local-function-frames* (when lexical *local-function-frames*))
        (*immediate-lambda-domains* (when lexical *immediate-lambda-domains*)))
    (multiple-value-bind (scope ordinary initializers)
        (analyze-lambda-scope build lambda-list domains :method method :returns #'form-return-summary
                             :specials (body-special-domains body))
      (declare (ignore ordinary))
      (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
        (reduce (lambda (old new) (merge-return-summaries build old new))
                (mapcan #'identity initializers)
                :initial-value (ordinary-return-summary build body))))))

;; These cold cells belong to one lexical source scope. They may occur in the
;; existing FUNCTION-BINDINGS alist, never in persistent value-domain facts or
;; emitted code. A saved local capture therefore retains its actual binder.
(defstruct local-function-binding name definition frame domains reachedp (summary :pending))
(defstruct local-function-frame
  form bindings outer-frames outer-functions arguments functions specials invariants
  method tags lambda-domains source-key solvingp changedp (version 0))

(defun find-local-function-binding (name)
  (loop for frame in *local-function-frames*
        for binding = (find name (local-function-frame-bindings frame)
                            :key #'local-function-binding-name :test #'name=)
        when binding return binding))

(defun call-in-local-function-environment (build frame definitionsp process)
  (let* ((group-p (or (not definitionsp) (eq (car (local-function-frame-form frame)) 'labels)))
         (*local-function-frames* (if group-p (cons frame (local-function-frame-outer-frames frame))
                                     (local-function-frame-outer-frames frame)))
         (*value-domain-local-functions*
           (if group-p (append (mapcar #'local-function-binding-name (local-function-frame-bindings frame))
                               (local-function-frame-outer-functions frame))
               (local-function-frame-outer-functions frame)))
         (*argument-domains* (local-function-frame-arguments frame))
         (*function-bindings* (local-function-frame-functions frame))
         (*declared-specials* (local-function-frame-specials frame))
         (*mutable-invariant-bindings* (local-function-frame-invariants frame))
         (*current-method* (local-function-frame-method frame))
         (*tagbody-targets* (local-function-frame-tags frame))
         (*immediate-lambda-domains* (local-function-frame-lambda-domains frame)))
    (with-build-source-key (build (local-function-frame-source-key frame))
      (funcall process))))

(defun flow-domain-covered-p (build actual expected)
  ;; Opacity is an origin envelope joined with UNKNOWN, not a native class.
  ;; A may-opaque profile covers clean inputs too; UNKNOWN cannot cover an
  ;; actual import origin which its body proof would otherwise reinterpret.
  (or (equal actual expected)
      (if (owned-record-domain-p expected)
          (and (owned-record-domain-p actual) (name= (second actual) (second expected)))
          (if (graph-node-domain-p expected)
              (and (graph-node-domain-p actual) (eql (second actual) (second expected))
                   (flow-domain-covered-p build (third actual) (third expected)))
              (if (external-result-domain-p expected)
                  ;; A may-opaque envelope covers clean callers too, but a
                  ;; shaped envelope requires geometry from every caller.
                  (or (eq (value-domain-shape build expected) :unknown)
                      (subtype-domain-p build actual (value-domain-shape build expected)))
                  (and (not (external-result-domain-p actual))
                       (or (eq expected :unknown) (subtype-domain-p build actual expected))))))))

(defun record-local-function-inputs (build binding domains)
  (let* ((frame (local-function-binding-frame binding))
         (previous (local-function-binding-domains binding))
         (reachedp (local-function-binding-reachedp binding)))
    (if (local-function-frame-solvingp frame)
        (let ((merged (if reachedp
                          (mapcar (lambda (old new) (merge-value-domains build old new)) previous domains)
                          domains)))
          (unless (and reachedp (equal previous merged))
            (setf (local-function-binding-domains binding) merged
                  (local-function-binding-reachedp binding) t
                  (local-function-frame-changedp frame) t)
            (incf (local-function-frame-version frame))))
        (unless (and reachedp
                     (every (lambda (actual expected)
                              (flow-domain-covered-p build actual expected)) domains previous))
          (fail build 'snowgrave:incomplete-domain :local-function-call-domain
                "A lexical call lacks its joined definition-site input proof." :reachability)))
    (local-function-binding-summary binding)))

(defun audit-local-function-capture (build binding)
  (call-in-local-function-environment
   build (local-function-binding-frame binding) t
   (lambda ()
     (let ((definition (local-function-binding-definition binding)))
       (record-local-function-inputs
        build binding (capture-lambda-domains build (second definition) :lexical t
                                              :specials (body-special-domains (cddr definition))))))))

(defun local-call-return-summary (build binding form)
  ;; Summarize caller expressions before switching to the definition's scope.
  ;; Defaults and AUX then see actual earlier parameters plus definition-site
  ;; captures, never the variable shadowing at this particular call site.
  (let* ((definition (local-function-binding-definition binding))
         (contract (lambda-contract build (second definition))))
    (multiple-value-bind (arguments bindings completep variable-tail)
        (if (member (car form) '(funcall apply multiple-value-call))
            (ordinary-call-argument-plan build form :required-count (length (getf contract :required)))
            (values (cdr form) nil t nil))
      (unless completep
        (unless *collect-function-flow*
          (fail build 'snowgrave:incomplete-domain :local-function-arguments
                "A lexical call needs a complete producer tuple or a proved APPLY prefix." :reachability))
        (return-from local-call-return-summary :pending))
      (let* ((*argument-domains* (append bindings *argument-domains*))
             (supplied (mapcar (lambda (argument) (value-domain build argument)) arguments)))
        (audit-lambda-parser-inputs build contract supplied variable-tail (local-function-binding-name binding))
        (when (< (length supplied) (length (getf contract :required)))
          ;; The ordinary local lambda parser owns this runtime arity error.
          ;; Retain its lexical definition even when no body tuple can run.
          (record-local-function-inputs
           build binding (make-list (length (lambda-input-variables contract)) :initial-element :unknown))
          (return-from local-call-return-summary :pending))
        (let ((domains
                (call-in-local-function-environment
                 build (local-function-binding-frame binding) t
                 (lambda ()
                   (call-lambda-domains build (second definition) supplied variable-tail
                                        :lexical t :specials (body-special-domains (cddr definition)))))))
          (record-local-function-inputs build binding domains))))))

(defun solve-local-function-scope (build form process &key package open next original local)
  "One scoped input/return fixed point serves all lexical-function walkers."
  (let* ((frame (make-local-function-frame
                 :form form :outer-frames *local-function-frames* :outer-functions *value-domain-local-functions*
                 :arguments *argument-domains* :functions *function-bindings* :specials *declared-specials*
                 :invariants *mutable-invariant-bindings* :method *current-method* :tags *tagbody-targets*
                 :lambda-domains *immediate-lambda-domains* :source-key (build-source-key build)))
         (generated (build-generated build)) (constructors (build-constructors build))
         (method-names (build-method-names build)) (sequence (build-sequence build))
         (dependencies (build-dependencies build))
         (collecting-p *collect-function-flow*) (changed-p *function-flow-changed*))
    (setf (local-function-frame-bindings frame)
          (mapcar (lambda (definition)
                    (make-local-function-binding :name (first definition) :definition definition :frame frame))
                  (second form)))
    (when open (setf (local-function-frame-solvingp frame) t))
    (unless open
      (unwind-protect
           (let ((*collect-function-flow* t) (*function-flow-changed* nil))
             (setf (local-function-frame-solvingp frame) t)
             (loop
               (setf (local-function-frame-changedp frame) nil
                     (build-generated build) generated (build-constructors build) constructors
                     (build-method-names build) method-names (build-sequence build) sequence
                     (build-dependencies build) dependencies)
               ;; The existing ordinary source walker discovers calls in tests,
               ;; defaults, side effects and nested closures as well as returns.
               (call-in-local-function-environment
                build frame nil
                (lambda ()
                  (transform-body build (cddr form) (or package (build-output-package build))
                                  :next next :original original :local *value-domain-local-functions*)))
               (dolist (binding (local-function-frame-bindings frame))
                 (when (local-function-binding-reachedp binding)
                   (call-in-local-function-environment
                    build frame t
                    (lambda ()
                      (let* ((definition (local-function-binding-definition binding))
                             (domains (local-function-binding-domains binding))
                             (body (cddr definition)))
                        (multiple-value-bind (scope ordinary)
                            (analyze-lambda-scope build (second definition) domains
                                                 :package (or package (build-output-package build))
                                                 :local *value-domain-local-functions* :next next :original original
                                                 :specials (body-special-domains body))
                          (declare (ignore ordinary))
                          (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
                            (transform-body build body (or package (build-output-package build))
                                            :next next :original original :local *value-domain-local-functions*)))
                        (let* ((previous (local-function-binding-summary binding))
                               (additional (lambda-return-summary build (second definition) domains body :lexical t))
                               (merged (merge-return-summaries build previous additional)))
                          (unless (same-return-summary-p previous merged)
                            (setf (local-function-binding-summary binding) merged
                                  (local-function-frame-changedp frame) t)
                            (incf (local-function-frame-version frame)))))))))
               (unless (local-function-frame-changedp frame)
                 ;; Global pending components must settle in their existing
                 ;; outer fixed point first. Final replay widens pure local
                 ;; cycles once, then propagates that conservative result.
                 (when (not collecting-p)
                   (dolist (binding (local-function-frame-bindings frame))
                     (when (local-function-binding-reachedp binding)
                       (let ((summary (local-function-binding-summary binding)))
                         (when (or (eq summary :pending)
                                   (member :pending (return-summary-domains summary)))
                           (setf (local-function-binding-summary binding)
                                 (if (eq summary :pending) (make-return-summary (list :unknown) nil)
                                     (make-return-summary (substitute :unknown :pending (return-summary-domains summary))
                                                          (return-summary-completep summary)))
                                 (local-function-frame-changedp frame) t)
                           (incf (local-function-frame-version frame)))))))
                 (unless (local-function-frame-changedp frame) (return))))
             (when (and (not collecting-p) *function-flow-changed*)
               (fail build 'snowgrave:incomplete-domain :local-function-flow-replay
                     "Final lexical replay introduced a caller absent from the shared outer fixed point." :reachability))
             (setf changed-p (or changed-p *function-flow-changed*)))
        (setf (local-function-frame-solvingp frame) nil
              (build-generated build) generated (build-constructors build) constructors
              (build-method-names build) method-names (build-sequence build) sequence
              (build-dependencies build) dependencies
              *function-flow-changed* changed-p)))
    (call-in-local-function-environment build frame nil (lambda () (funcall process frame)))))

(defun local-function-context-key (build)
  ;; These are cold domain facts, not runtime lexical values. Preserve exact
  ;; owner-cell versions and mutable binder identities across replay views.
  (list (build-source-key build) (copy-tree *argument-domains*) (copy-tree *function-bindings*)
        *value-domain-local-functions*
        (mapcar (lambda (frame) (cons frame (local-function-frame-version frame))) *local-function-frames*)
        *declared-specials* *current-method* *tagbody-targets* *immediate-lambda-domains*
        (mapcar (lambda (fact)
                  (list (first fact) (second fact) (copy-tree (third fact)) (fourth fact) (fifth fact)))
                *mutable-invariant-bindings*)))

(defun mutable-local-function-context-p ()
  ;; Initial custody facts never change after binding. A body fixed point
  ;; can widen its candidate facts in place, so only that context disables
  ;; lexical memoization; the immutable facts remain part of the cache key.
  (some (lambda (fact) (not (eq (fifth fact) :initial))) *mutable-invariant-bindings*))

(defun call-with-local-function-scope (build form process &rest options &key open &allow-other-keys)
  ;; A memo belongs only to this lexical solve and its nested scopes. Source
  ;; node identity is qualified by captured facts and visible frame versions;
  ;; no table survives a root traversal or a global fixed-point iteration.
  (let* ((open (or open (not (and (build-output-package build)
                                 (build-function-domains build) (build-function-returns build)))))
         ;; Open-source normalization may ask for a return view before the
         ;; closed caller fixed point exists. It must not run a closed scratch
         ;; emission or invent output names during that earlier phase.
         (*local-function-scope-cache* (or *local-function-scope-cache* (make-hash-table :test #'eq)))
         (key (local-function-context-key build))
         (cached (unless (or open (mutable-local-function-context-p))
                   (assoc key (gethash form *local-function-scope-cache*) :test #'equal))))
    (if cached
        (call-in-local-function-environment build (second cached) nil (lambda () (funcall process (second cached))))
        (apply #'solve-local-function-scope build form
               (lambda (frame)
                 (unless (or open (mutable-local-function-context-p))
                   (push (list key frame) (gethash form *local-function-scope-cache*)))
                 (funcall process frame)) :open open options))))
(defun source-call-return-summary (build name &optional global-targets relations-p)
  (when (and (build-function-returns build)
             (or (not (member-name name *value-domain-local-functions*))
                 (member-name name global-targets)))
    (let ((summary
            (cond ((or (ordinary-function-form build name)
                       (member-name name (getf (build-declaration build) :closed-generics)))
                   (gethash name (build-function-returns build) :pending))
                  ((member-name name (getf (build-declaration build) :external-operations))
                   (let ((contract (assoc name (getf (build-declaration build) :external-return-domains) :test #'name=)))
                     (if contract (make-return-summary (copy-tree (second contract)) t)
                         (make-return-summary (list :external-result) nil)))))))
      ;; Formal selectors belong to the callee row. Only an actual call
      ;; receipt may substitute them; free type/initializer queries project.
      (if (or relations-p (not (return-summary-p summary))) summary
          (make-return-summary (mapcar #'relational-base (return-summary-domains summary))
                               (return-summary-completep summary))))))

(defun indirect-call-opaque-input-p (build form callee-domain)
  ;; The saved callee fact and actual inputs share one provenance owner.
  ;; MVC consumes every producer value, including secondary values and the
  ;; opaque domains of incomplete return tails, rather than only its primary.
  (or (external-result-domain-p callee-domain)
      (some (lambda (input)
              (if (eq (car form) 'multiple-value-call)
                  (let ((summary (form-return-summary build input)))
                    (some #'external-result-domain-p
                          (if (return-summary-p summary) (return-summary-domains summary) (list summary))))
                  (external-result-domain-p (value-domain build input))))
            (cddr form))))

(defun indirect-call-return-summary (build form targets global-targets callee-domain)
  "Compose source return contracts, retaining opaque inputs of unowned targets."
  ;; A helper's unsolved callback result has not supplied an arbitrary target.
  ;; The shared fixed point must discover it (or settle it to UNKNOWN) before
  ;; its result can contribute an opaque normal-return envelope.
  (when (eq (relational-base callee-domain) :pending)
    (return-from indirect-call-return-summary :pending))
  (let* ((summaries (mapcar (lambda (name)
                              (if (local-function-binding-p name) (local-call-return-summary build name form)
                                  (source-call-return-summary build name global-targets))) targets))
         (unowned-p (or (null targets) (some #'null summaries)))
         (fallback (when unowned-p
                     (make-return-summary
                      (list (if (indirect-call-opaque-input-p build form callee-domain)
                                :external-result :unknown)) nil))))
    ;; Known summaries already own returned input provenance. For any other
    ;; target the fallback composes opaque inputs here, without walking the
    ;; saved callee subtree again or treating UNKNOWN as native proof.
    (if targets
        (reduce (lambda (old summary) (merge-return-summaries build old (or summary fallback)))
                summaries :initial-value :pending)
        fallback)))

(defun assignment-return-summary (build form)
  (let* ((pair (last (cdr form) 2)) (place (first pair)) (value (second pair))
         (setter (when (and (eq (first form) 'setf) (consp place)) (list 'setf (first place))))
         (binding (when setter (find-local-function-binding setter))))
    (cond ((null pair) (make-return-summary (list '(eql nil)) t))
          (binding (local-call-return-summary build binding (list* setter value (cdr place))))
          ((and setter (source-call-return-summary build setter)) (source-call-return-summary build setter))
          (t (make-return-summary (list (value-domain build value)) t)))))

(defun source-truth (build form)
  (let ((domain (value-domain build form)))
    (when (and (consp domain) (eq (car domain) 'eql))
      (if (null (cadr domain)) :false :true))))

(defun standard-operation-meaning-p (build name &optional local global-targets)
  (and (not (or (member-name name (build-functions build))
                (member-name name (getf (build-declaration build) :closed-generics))))
       (or (not (or (member-name name local) (member-name name *value-domain-local-functions*)))
           ;; Reuse the callee's qualified value proof. Argument expressions
           ;; retain their own lexical scope; no callee subtree is revisited.
           (member-name name global-targets))))

(defun predicate-refined-domains (build test truep &optional local)
  "Use only a positive actual class test on a stable lexical value.
This proves a branch, not a field declaration or arbitrary external alias ABI."
  (cond
    ((and truep (consp test) (= (length test) 2)
          (standard-operation-meaning-p build (car test) local)
          (symbolp (second test)) (assoc (second test) *argument-domains*)
          (not (special-variable-p build (second test)))
          (find (car test) (getf (build-declaration build) :external-value-guards) :key #'second :test #'name=))
     (let ((guard (find (car test) (getf (build-declaration build) :external-value-guards) :key #'second :test #'name=)))
       (acons (second test) (list :external-value (first guard)) *argument-domains*)))
    ((and (consp test) (member (car test) '(not null)) (= (length test) 2)
          (standard-operation-meaning-p build (car test) local))
     (predicate-refined-domains build (second test) (not truep) local))
    ((and (consp test) (or (and (eq (car test) 'and) truep) (and (eq (car test) 'or) (not truep))))
     (let ((*argument-domains* *argument-domains*))
       (dolist (part (cdr test) *argument-domains*)
         (setf *argument-domains* (predicate-refined-domains build part truep local)))))
    ((and truep (consp test) (eq (car test) 'typep) (= (length test) 3)
          (standard-operation-meaning-p build 'typep local)
          (symbolp (second test)) (assoc (second test) *argument-domains*)
          (not (special-variable-p build (second test))))
     (multiple-value-bind (class quotedp) (quoted-value (third test))
       (if (and quotedp (or (member-name class (build-classes build))
                           (native-value-type-p class) (member class '(list vector))))
           (let* ((previous (binding-value-domain (second test)))
                  (refined
                    (cond ((and (member class '(list vector))
                                (external-value-observation-p build previous)) previous)
                          ((subtype-domain-p build previous class) previous)
                          ((member class '(list vector)) (qualify-domain-origin class previous))
                          (t class))))
             (acons (second test) refined *argument-domains*))
           *argument-domains*)))
    (t *argument-domains*)))

(defmacro with-predicate-domains ((build test truep &optional local) &body body)
  `(let ((*argument-domains* (predicate-refined-domains ,build ,test ,truep ,local))) ,@body))

(defun settle-return-summary (build name)
  (let ((summary (gethash name (build-function-returns build) :pending)))
    (cond ((eq summary :pending)
           (setf (gethash name (build-function-returns build)) (make-return-summary (list :unknown) nil :havoc)
                 *function-flow-changed* t))
          ((member :pending (return-summary-domains summary))
           (setf (gethash name (build-function-returns build))
                 (make-return-summary (substitute :unknown :pending (return-summary-domains summary))
                                      (return-summary-completep summary) :havoc)
                 *function-flow-changed* t))
          ((pending-record-flow-effects-p (return-summary-effects summary))
           (setf (return-summary-effects summary) :havoc *function-flow-changed* t)))))

(defun return-summary-evidence (summary)
  (list :primary-return-domain (copy-tree (return-summary-primary summary))
        :returned-value-domains
        (when (and (return-summary-p summary) (return-summary-completep summary))
          (copy-tree (return-summary-domains summary)))
        :returned-value-count-complete-p (and (return-summary-p summary) (return-summary-completep summary))))

(defun conditional-clauses (build form)
  (unless (and (snowgrave::source-finite-list-p (cdr form))
               (every (lambda (clause) (and (consp clause) (snowgrave::source-finite-list-p clause))) (cdr form)))
    (fail build 'snowgrave:unsupported-definition :conditional-clause
          "COND requires finite nonempty proper clauses." :source-admission))
  (cdr form))

(defun case-clauses (build form)
  ;; Keys are literal list designators, never executable forms. One grammar
  ;; owns source traversal, ordinary rewriting and return-flow composition.
  (unless (and (consp (cdr form)) (snowgrave::source-finite-list-p (cdr form))
               (every (lambda (clause)
                        (and (consp clause) (snowgrave::source-finite-list-p clause)
                             (if (consp (car clause))
                                 (and (snowgrave::source-finite-list-p (car clause))
                                      (every #'serializable-tree-p (car clause)))
                                 (serializable-tree-p (car clause))))) (cddr form)))
    (fail build 'snowgrave:unsupported-definition :case-clause
          "CASE/ECASE require a selector and finite proper clauses with readable literal keys." :source-admission))
  (when (and (eq (car form) 'case)
             (some (lambda (clause) (member (car clause) '(t otherwise))) (butlast (cddr form))))
    (fail build 'snowgrave:unsupported-definition :case-clause
          "A CASE default clause must be last." :source-admission))
  (cddr form))

(defun case-return-summary (build form)
  (let* ((clauses (case-clauses build form)) (selector (cadr form))
         (domain (value-domain build selector))
         (known (and (consp domain) (eq (car domain) 'eql)))
         (key (if known (cadr domain) selector)))
    ;; Infer exact EQL only for scalar constants, whose identity survives the
    ;; ordinary two-pass compiler. Heap literal coalescing is not a proof.
    (multiple-value-bind (quoted quotedp) (quoted-value selector)
      (when quotedp (setf known t key quoted)))
    (setf known (and (or known (numberp selector) (characterp selector))
                     (or (symbolp key) (numberp key) (characterp key))))
    (labels ((defaultp (clause) (and (eq (car form) 'case) (member (car clause) '(t otherwise))))
             (unmatched () (if (eq (car form) 'case) (make-return-summary (list '(eql nil)) t) :pending))
             (keys (clause) (let ((keys (car clause))) (if (listp keys) keys (list keys)))))
      (if known
          (let ((selected (find-if (lambda (clause)
                                     (or (defaultp clause) (member key (keys clause) :test #'eql))) clauses)))
            (if selected (body-return-summary build (cdr selected))
                (unmatched)))
          (reduce (lambda (summary clause)
                    (if (or (defaultp clause) (keys clause))
                        (merge-return-summaries build summary (body-return-summary build (cdr clause))) summary))
                  clauses :initial-value (if (some #'defaultp clauses) :pending (unmatched)))))))

(defun logical-return-summary (build operator arguments)
  ;; Nonfinal tests supply one primary value; only the final operand can
  ;; forward its complete tuple. Do not treat all OR operands as tuple exits.
  (cond ((null arguments) (make-return-summary (list (list 'eql (eq operator 'and))) t))
        ((null (cdr arguments)) (form-return-summary build (car arguments)))
        (t (let* ((truth (source-truth build (car arguments)))
                  (short (if (eq operator 'and) (make-return-summary (list '(eql nil)) t)
                             (make-return-summary (list (value-domain build (car arguments))) t))))
             (cond ((eq truth (if (eq operator 'and) :false :true)) short)
                   ((eq truth (if (eq operator 'and) :true :false))
                    (with-predicate-domains (build (car arguments) (eq operator 'and))
                      (logical-return-summary build operator (cdr arguments))))
                   (t (merge-return-summaries build short
                         (with-predicate-domains (build (car arguments) (eq operator 'and))
                           (logical-return-summary build operator (cdr arguments))))))))))

(defun destructuring-source-scope (build form)
  (let* ((variables (required-binding-variables build form))
         (domain (if (external-result-domain-p (value-domain build (caddr form))) :external-result :unknown)))
    (cons (append (mapcar (lambda (variable) (cons variable domain)) variables) *argument-domains*)
          (append (mapcar (lambda (variable) (cons variable :unknown)) variables) *function-bindings*))))

(defmacro with-destructuring-source-facts ((build form) &body body)
  (let ((scope (gensym "DESTRUCTURING-SCOPE")))
    `(let* ((,scope (destructuring-source-scope ,build ,form))
            (*argument-domains* (car ,scope)) (*function-bindings* (cdr ,scope))) ,@body)))

(defun form-return-summary (build form)
  (when (and *cold-recipe-source-marker* (consp form) (eq (car form) *cold-recipe-source-marker*))
    (return-from form-return-summary (form-return-summary build (second form))))
  (let ((receipt (and (consp form) (assoc form *flow-value-receipts* :test #'eq))))
    (when receipt (return-from form-return-summary (cdr receipt))))
  (when (and *effective-method-emitter* (consp form) (eq (first form) 'call-method))
    ;; An early binder/default query has not executed the CALL-METHOD leaf.
    ;; Its normal value count and origin are unknown until the composer gives
    ;; the source walker the actual receipt. Never treat its MOP inputs as
    ;; ordinary arguments or interpret missing information as clean UNKNOWN.
    (return-from form-return-summary (make-return-summary (list :external-result) nil)))
  (if (and *initialization-phase* (initialization-effectful-form-p build form))
      ;; Binder queries precede actual source evaluation. A phase-dependent
      ;; effectful value cannot borrow the receiver's earlier/later row. Keep
      ;; tuple bottom/count proof and independently native results. Only a
      ;; phase-dependent value needs the conservative origin envelope.
      (let* ((*initialization-phase* nil)
             (summary (form-return-summary-code build form)))
        (if (return-summary-p summary)
            (make-return-summary
             (mapcar (lambda (domain)
                       (independent-record-flow-result-domain build domain))
                     (return-summary-domains summary))
             (return-summary-completep summary)) summary))
      (form-return-summary-code build form)))

(defun form-return-summary-code (build form)
  "Use one existing helper return fixed point for primary and ordered values.
Position unions describe ordinary MVB bindings, including NIL padding only
from a complete shorter result. Different counts stay incomplete for calls.
Unknown/native operations retain only their existing primary fact."
  (cond
    ;; These cold leaves replace CALL-METHOD nodes only in the proof tree
    ;; returned alongside actual CEM code. They never enter emitted source.
    ((and *effective-return-proof* (return-summary-p form)) form)
    ((atom form) (make-return-summary (list (value-domain build form)) t))
    ((member (car form) '(quote function)) (make-return-summary (list (value-domain build form)) t))
    ((member (car form) '(setq setf)) (assignment-return-summary build form))
    ((eq (car form) 'values)
     (unless (snowgrave::source-finite-list-p (cdr form))
       (fail build 'snowgrave:unsupported-definition :multiple-value-producer
             "An explicit VALUES producer requires a finite proper argument list." :source-admission))
     (make-return-summary (mapcar (lambda (argument) (value-domain build argument)) (cdr form)) t))
    ((member (car form) '(multiple-value-prog1 unwind-protect)) (form-return-summary build (cadr form)))
    ((member (car form) '(progn locally)) (body-return-summary build (cdr form)))
    ((eq (car form) 'block) (ordinary-return-summary build (cddr form)))
    ((member (car form) '(return-from go)) :pending)
    ((eq (car form) 'tagbody) (make-return-summary (list '(eql nil)) t))
    ((eq (car form) 'the)
     (let ((summary (form-return-summary build (third form))))
       (if (and (return-summary-p summary) (return-summary-domains summary))
           (make-return-summary (cons (value-domain build form) (cdr (return-summary-domains summary)))
                                (return-summary-completep summary))
           summary)))
    ((and (eq (car form) 'error) (not (member-name 'error *value-domain-local-functions*))) :pending)
    ((and (eq (car form) 'call-next-method) *current-method* (null (cdr form)))
     (fourth *current-method*))
    ((eq (car form) 'if)
     (case (source-truth build (cadr form))
       (:true (with-predicate-domains (build (cadr form) t) (form-return-summary build (caddr form))))
       (:false (with-predicate-domains (build (cadr form) nil) (form-return-summary build (cadddr form))))
       (t (merge-return-summaries build
            (with-predicate-domains (build (cadr form) t) (form-return-summary build (caddr form)))
            (with-predicate-domains (build (cadr form) nil) (form-return-summary build (cadddr form)))))))
    ((eq (car form) 'cond)
     (let ((summary (make-return-summary (list '(eql nil)) t)))
       (dolist (clause (reverse (conditional-clauses build form)) summary)
         (let* ((truth (source-truth build (car clause)))
                (branch (if (cdr clause) (with-predicate-domains (build (car clause) t) (body-return-summary build (cdr clause)))
                            (make-return-summary (list (value-domain build (car clause))) t))))
           (case truth
             (:false nil) (:true (setf summary branch))
             (t (setf summary (merge-return-summaries build branch summary))))))))
    ((member (car form) '(case ecase)) (case-return-summary build form))
    ((member (car form) '(and or)) (logical-return-summary build (car form) (cdr form)))
    ((member (car form) '(when unless))
     (form-return-summary build (if (eq (car form) 'when)
                                   `(if ,(cadr form) (progn ,@(cddr form)) nil)
                                   `(if ,(cadr form) nil (progn ,@(cddr form))))))
    ((member (car form) '(let let*))
     (multiple-value-bind (scope analyzed)
         (analyze-let-scope build (cadr form) (eq (car form) 'let*) #'identity
                            :specials (body-special-domains (cddr form)))
       (declare (ignore analyzed))
       (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
         (body-return-summary build (cddr form)))))
    ((eq (car form) 'multiple-value-bind)
     (multiple-value-bind (scope analyzed)
         (analyze-multiple-value-scope build (cadr form) (caddr form) #'identity)
       (declare (ignore analyzed))
       (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
         (body-return-summary build (cdddr form)))))
    ((eq (car form) 'destructuring-bind)
     (with-destructuring-source-facts (build form)
       (body-return-summary build (cdddr form))))
    ((immediate-lambda-form build form)
     (immediate-lambda-return-summary build form))
    ((member (car form) '(flet labels))
     (call-with-local-function-scope
      build form (lambda (frame) (declare (ignore frame)) (ordinary-return-summary build (cddr form)))))
    ((find-local-function-binding (car form))
     (local-call-return-summary build (find-local-function-binding (car form)) form))
    ((and (build-function-returns build) (member (car form) '(funcall apply multiple-value-call)))
     (multiple-value-bind (targets global-targets callee-domain) (known-function-targets build (second form))
       (multiple-value-bind (ordinary precise-p)
           (ordinary-indirect-result-domain build form targets global-targets)
         (if precise-p
             (make-return-summary
              (list ordinary)
              (every (lambda (target) (ordinary-single-value-result-p build target global-targets)) targets))
             (indirect-call-return-summary build form targets global-targets callee-domain)))))
    ((source-call-return-summary build (car form)) (source-call-return-summary build (car form)))
    ((and (eq (first form) 'make-instance) (graph-state-profile-p build))
     (let ((domain (source-construction-domain build form)))
       (make-return-summary (list domain) (owned-record-domain-p domain))))
    ((member (car form) '(slot-value snowgrave::%record-read))
     (multiple-value-bind (domain boundp) (record-slot-read-domain build (second form) (third form))
       ;; A pending incoming state supplies no normal return/count yet. It
       ;; must not permanently widen an eventual bound single-value read.
       (cond ((eq domain :pending) :pending)
             (boundp (make-return-summary (list (value-domain build form)) t))
             (t (make-return-summary (list (value-domain build form)) nil)))))
    ((or (ordinary-single-value-result-p build (car form))
         (and (member (car form) '(typep slot-boundp))
              (standard-operation-meaning-p build (car form))))
     (make-return-summary (list (value-domain build form)) t))
    (t (make-return-summary (list (value-domain build form)) nil))))

(defun analyze-multiple-value-scope (build variables producer process &key open specials)
  (snowgrave::analyze-source-multiple-value-bindings
   variables producer (cons (copy-tree *argument-domains*) (copy-list *function-bindings*))
   (lambda (form scope)
     (let* ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
       (multiple-value-bind (code receipt) (funcall process form)
        (let* ((summary (or receipt (form-return-summary build form)))
            (completep (and (return-summary-p summary) (return-summary-completep summary)))
            ;; An incomplete summary still owns the ordinary primary value,
            ;; which is exactly MVB's first binding (including zero-value NIL).
            ;; Other proved positions may survive variable-count joins, with
            ;; their possible padding included; no missing tail is invented.
            (domains (cond ((eq summary :pending)
                            ;; No returned position is known yet. Preserve
                            ;; lattice bottom for each requested binding;
                            ;; this does not prove a count or NIL padding.
                            (make-list (length variables) :initial-element :pending))
                           ((return-summary-p summary) (return-summary-domains summary))))
            (literalp (and (consp form) (eq (car form) 'values)))
            (arguments (when literalp (cdr form))))
       ;; An unclassified external result has an unknown native tail, not an
       ;; ordinary UNKNOWN tail that may be reinterpreted as a closed class.
       (when (and (not completep) (some #'external-result-domain-p domains))
         (setf domains (append domains (make-list (max 0 (- (length variables) (length domains)))
                                                 :initial-element :external-result))))
       (unless open
         (loop for name in variables for tail = arguments then (cdr tail)
               for returned = domains then (cdr returned) do
           (when (external-shared-binding-p build name specials)
             (audit-external-shared-binding
              build name (and (or returned completep)
                              (if literalp (native-data-form-p build (car tail))
                                  (native-data-domain-p build (if returned (car returned) '(eql nil))))) specials))))
       (values (loop for domain in domains for tail = arguments then (cdr tail)
                     collect (cons domain (if literalp (function-expression-target (car tail)) :unknown)))
               code completep)))))
   (lambda (name kind fact scope)
     (let ((fact (case kind (:provided fact) (:missing (cons '(eql nil) :unknown))
                       (:unknown (cons :unknown :unknown)))))
       (cons (acons name (car fact) (car scope)) (acons name (cdr fact) (cdr scope)))))
   :source-key (build-source-key build) :path (list (build-identity build))))

(defun multiple-value-call-plan (build producers &key (literal-proofs t))
  "Describe a finite complete producer tuple without executing its proof forms.
Runtime bindings preserve each original producer; opaque domain facts feed the
existing call audits. Literal VALUES keeps its stronger source-tree proofs.
The fifth value distinguishes pending producers from genuine incomplete counts."
  (let (arguments bindings domains)
    (dolist (producer producers)
      (let ((summary (form-return-summary build producer)))
        (when (eq summary :pending)
          (return-from multiple-value-call-plan (values nil nil nil nil t)))
        (unless (and (return-summary-p summary) (return-summary-completep summary))
          (return-from multiple-value-call-plan (values nil nil nil nil)))
        (let* ((positions (return-summary-domains summary))
               (variables (loop repeat (length positions) collect (gensym "RETURNED-ARGUMENT")))
               (literalp (and literal-proofs (consp producer) (eq (car producer) 'values))))
          (push (list variables producer) bindings)
          (loop for variable in variables for domain in positions
                for literal = (when literalp (cdr producer)) then (cdr literal)
                do (push (cons variable domain) domains)
                   (push (cond (literalp (car literal))
                               ((and (consp domain) (eq (car domain) 'eql))
                                (if (or (keywordp (cadr domain)) (member (cadr domain) '(nil t))
                                        (numberp (cadr domain)) (characterp (cadr domain)))
                                    (cadr domain) (list 'quote (cadr domain))))
                               (t variable)) arguments)))))
    (values (nreverse arguments) (nreverse bindings) domains t)))

(defun indirect-argument-audit-p (build name local global-targets)
  ;; A global callable value retains its owner inside a same-name FLET.
  ;; This decides the callee's audit, never the argument expressions' scope.
  (or (local-function-binding-p name)
      (member-name name (getf (build-declaration build) :closed-generics))
      (and (or (not (member-name name local)) (member-name name global-targets))
           (or (ordinary-function-form build name)
               (member name '(eq eql equal equalp))
               (member name *representation-sensitive-ordinary-operations*)
               (member-name name (getf (build-declaration build) :external-operations))))))

(defun body-special-domains (body) (snowgrave:source-body-special-domains body))
(defun split-source-body (body) (snowgrave:source-body-parts body))
(defun preserve-source-block (name body) (snowgrave:source-block-body name body))

(defun body-value-domain (build body)
  (with-source-body-facts (body)
    (value-domain build (car (last (remove-if (lambda (form)
                                              (and (consp form) (eq (car form) 'declare))) body))))))

(defun required-binding-variables (build form)
  (snowgrave:source-required-binding-variables
   (cadr form) :nested (eq (car form) 'destructuring-bind)
   :source-key (build-source-key build) :path (list (build-identity build))))

(defun handler-binding-variables (build clause)
  (snowgrave:source-required-binding-variables
   (cadr clause) :source-key (build-source-key build) :path (list (build-identity build))))

(defun source-return-domains (build forms &optional (describe #'value-domain))
  "Conservatively collect every explicit nonlocal primary return.
Targets are deliberately merged: an inner BLOCK return may broaden the
summary, but cannot hide a return out of the ordinary function or its cleanup."
  (labels ((walk-body (body)
             (with-source-body-facts (body)
               (mapcan #'walk body)))
           (walk-local-definition (frame binding)
             (when (local-function-binding-reachedp binding)
               (call-in-local-function-environment
                build frame t
                (lambda ()
                  (let ((definition (local-function-binding-definition binding)))
                    (multiple-value-bind (scope ordinary initializers)
                        (analyze-lambda-scope
                         build (second definition) (local-function-binding-domains binding)
                         :returns describe :specials (body-special-domains (cddr definition)))
                      (declare (ignore ordinary))
                      (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
                        (nconc (mapcan #'identity initializers) (walk-body (cddr definition))))))))))
           (walk (form)
             (cond
               ((atom form) nil)
               ((member (car form) '(quote declare)) nil)
               ((eq (car form) 'locally) (walk-body (cdr form)))
               ((eq (car form) 'return-from)
                (cons (funcall describe build (caddr form)) (walk (caddr form))))
               ((eq (car form) 'if)
                (nconc (walk (second form))
                       (with-predicate-domains (build (second form) t) (walk (third form)))
                       (with-predicate-domains (build (second form) nil) (walk (fourth form)))))
               ((member (car form) '(and or))
                (labels ((terms (arguments)
                           (when arguments
                             (nconc (walk (car arguments))
                                    (with-predicate-domains (build (car arguments) (eq (car form) 'and))
                                      (terms (cdr arguments)))))))
                  (terms (cdr form))))
               ((member (car form) '(when unless))
                (nconc (walk (second form))
                       (with-predicate-domains (build (second form) (eq (car form) 'when))
                         (walk-body (cddr form)))))
               ((eq (car form) 'cond)
                (mapcan (lambda (clause) (nconc (walk (car clause))
                                         (with-predicate-domains (build (car clause) t) (walk-body (cdr clause)))))
                        (conditional-clauses build form)))
               ((member (car form) '(case ecase))
                (nconc (walk (cadr form)) (mapcan (lambda (clause) (walk-body (cdr clause)))
                                                (case-clauses build form))))
               ((member (car form) '(let let*))
                (multiple-value-bind (scope analyzed)
                    (analyze-let-scope build (cadr form) (eq (car form) 'let*) #'walk
                                       :specials (body-special-domains (cddr form)))
                  (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
                    (nconc (mapcan #'second analyzed) (walk-body (cddr form))))))
               ((member (car form) '(flet labels))
                (call-with-local-function-scope
                 build form
                 (lambda (frame)
                   ;; MAPCAN consumes newly collected escape lists. The
                   ;; frame's binding list is only its input, never a result.
                   (nconc (mapcan (lambda (binding) (walk-local-definition frame binding))
                                  (local-function-frame-bindings frame))
                          (walk-body (cddr form))))))
               ((eq (car form) 'lambda)
                (multiple-value-bind (scope ordinary initializers)
                    (analyze-lambda-scope build (cadr form) nil :returns describe
                                         :specials (body-special-domains (cddr form)))
                  (declare (ignore ordinary))
                  (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
                    (nconc (mapcan #'identity initializers) (walk-body (cddr form))))))
               ((eq (car form) 'multiple-value-bind)
                (multiple-value-bind (scope returns)
                    (analyze-multiple-value-scope build (cadr form) (caddr form) #'walk)
                  (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
                    (nconc returns (walk-body (cdddr form))))))
               ((eq (car form) 'destructuring-bind)
                (nconc (walk (caddr form))
                       (with-destructuring-source-facts (build form)
                         (walk-body (cdddr form)))))
               ((eq (car form) 'handler-case)
                (nconc (walk (cadr form))
                       (mapcan (lambda (clause)
                                 (let ((*argument-domains*
                                         (append (mapcar (lambda (variable) (cons variable :unknown))
                                                         (handler-binding-variables build clause)) *argument-domains*)))
                                   (walk-body (cddr clause)))) (cddr form))))
               (t (mapcan #'walk (cdr form))))))
    (mapcan #'walk forms)))

(defun primary-return-domain (build body)
  (with-source-body-facts (body)
    (reduce (lambda (previous additional) (merge-value-domains build previous additional))
            (source-return-domains build body) :initial-value (body-value-domain build body))))

(defun ordinary-primary-return-domain (build body)
  (multiple-value-bind (prefix executable) (split-source-body body)
    (with-source-body-facts (prefix)
      (primary-return-domain build executable))))

(defun value-domain (build form)
  (when (and *cold-recipe-source-marker* (consp form) (eq (car form) *cold-recipe-source-marker*))
    (return-from value-domain (value-domain build (second form))))
  (let ((receipt (and (consp form) (assoc form *flow-value-receipts* :test #'eq))))
    (when receipt (return-from value-domain (return-summary-primary (cdr receipt)))))
  (when (and *effective-method-emitter* (consp form) (eq (first form) 'call-method))
    (return-from value-domain :external-result))
  (when (and *initialization-phase* (initialization-effectful-form-p build form)
             (not (eq (first form) 'make-instance)))
    (return-from value-domain (return-summary-primary (form-return-summary build form))))
  ;; One return lattice carries unclassified native results through ordinary
  ;; constructors/projections as well as helpers and joins. A proved native
  ;; result (for example a predicate boolean) ends this dependence. UNKNOWN
  ;; never does. Quoted/code data are not evaluated result dependencies.
  ;; The raw owner returns a second value when it already composed all result
  ;; inputs. Do not walk those inputs again: nested unknown projections must
  ;; cost one analysis per node, not two copies of each child subtree.
  (multiple-value-bind (domain result-inputs-covered-p) (raw-value-domain build form)
    (if (and (consp form)
             (not result-inputs-covered-p)
             (not (external-result-domain-p domain))
             ;; These have lexical/control semantics owned by the return
             ;; composer below; their syntactic inputs are not all returned.
             (not (member (car form) '(quote function values load-time-value let let* multiple-value-bind destructuring-bind flet labels
                                      locally block return-from if cond case ecase when unless
                                      and or progn unwind-protect multiple-value-prog1)))
             (not (native-data-domain-p build domain))
             (some (lambda (part) (external-result-domain-p (value-domain build part))) (cdr form)))
        :external-result domain)))

(defun raw-value-domain (build form)
  (cond ((and *effective-return-proof* (return-summary-p form)) (return-summary-primary form))
        ((numberp form) (type-of form))
        ((stringp form) 'string)
        ((arrayp form) (type-of form))
        ((characterp form) 'character)
        ((or (keywordp form) (eq form t) (null form)) (list 'eql form))
        ((symbolp form) (if (special-variable-p build form) :unknown
                           (binding-value-domain form)))
        ((and (consp form) (member (car form) '(setq setf)))
         (values (return-summary-primary (assignment-return-summary build form)) t))
        ((and (consp form) (member (car form) '(progn locally)))
         (body-value-domain build (cdr form)))
        ((and (consp form) (eq (car form) 'block))
         (primary-return-domain build (cddr form)))
        ((and (consp form) (member (car form) '(return-from go))) :pending)
        ((and (consp form) (eq (car form) 'tagbody)) '(eql nil))
        ((and (consp form) (eq (car form) 'the))
         (let ((input (value-domain build (third form))))
           (values (cond ((external-result-domain-p input) input)
                         ((member (second form) '(list cons)) (second form))
                         (t input)) t)))
        ((and (consp form) (eq (car form) 'if))
         (return-summary-primary (form-return-summary build form)))
        ((and (consp form) (eq (car form) 'next-method-p) *current-method*)
         (list 'eql (third *current-method*)))
        ((and (consp form) (eq (car form) 'call-next-method) *current-method* (null (cdr form)))
         (return-summary-primary (fourth *current-method*)))
        ((and (consp form) (member (car form) '(cond case ecase when unless and or)))
         (return-summary-primary (form-return-summary build form)))
        ((and (consp form) (member (car form) '(values multiple-value-prog1 unwind-protect)))
         (value-domain build (cadr form)))
        ((and (consp form) (member (car form) '(let let*)))
         (multiple-value-bind (scope analyzed)
             (analyze-let-scope build (cadr form) (eq (car form) 'let*) #'identity
                                :specials (body-special-domains (cddr form)))
           (declare (ignore analyzed))
           (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
             (body-value-domain build (cddr form)))))
        ((and (consp form) (eq (car form) 'multiple-value-bind))
         (multiple-value-bind (scope analyzed)
             (analyze-multiple-value-scope build (cadr form) (caddr form) #'identity)
           (declare (ignore analyzed))
           (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
             (body-value-domain build (cdddr form)))))
        ((and (consp form) (eq (car form) 'destructuring-bind))
         (with-destructuring-source-facts (build form) (body-value-domain build (cdddr form))))
        ((and (consp form) (member (car form) '(flet labels)))
         (call-with-local-function-scope
          build form (lambda (frame) (declare (ignore frame))
                       (return-summary-primary (ordinary-return-summary build (cddr form))))))
        ((and (consp form) (find-local-function-binding (car form)))
         (values (return-summary-primary
                  (local-call-return-summary build (find-local-function-binding (car form)) form)) t))
        ((and (consp form) (or (eq (car form) 'slot-value)
                                    (and *generated-class-operation* (eq (car form) 'snowgrave::%record-read))))
         (record-slot-read-domain build (second form) (third form)))
        ((and (graph-state-profile-p build) (consp form) (eq (car form) 'slot-boundp))
         (values 'boolean t))
        ((and (graph-state-profile-p build) (consp form) (eq (car form) 'slot-makunbound))
         (values (value-domain build (second form)) t))
        ((and (consp form) (eq (car form) 'quote))
         (if (or (symbolp (cadr form)) (numberp (cadr form)) (characterp (cadr form)))
             (list 'eql (cadr form)) (type-of (cadr form))))
        ((and (consp form) (eq (car form) 'function))
         ;; Enrich the existing value lattice with exact static source identity,
         ;; rather than adding a parallel callable fixed point or domain table.
         (if (and (snowgrave::source-name-p (second form))
                  (not (member-name (second form) *value-domain-local-functions*)))
             (list :function-target (second form)) :unknown))
        ((and (consp form) (eq (car form) 'load-time-value))
         (let ((*argument-domains* nil) (*function-bindings* nil)
               (*declared-specials* nil) (*value-domain-local-functions* nil) (*local-function-frames* nil)
               (*immediate-lambda-domains* nil))
           (value-domain build (second form))))
        ((and (consp form) (standard-operation-meaning-p build (car form))
              (member (car form) '(typep integerp rationalp floatp realp complexp stringp characterp
                                  vectorp arrayp symbolp consp listp endp null not keywordp numberp
                                  = /= < > <= >= eq eql equal equalp))) 'boolean)
        ((and (consp form) (standard-operation-meaning-p build (car form))
              (member (car form) '(+ - * / 1+ 1- max min abs mod rem))) 'number)
        ((and (consp form) (ordinary-scalar-result-domain build (car form)))
         (ordinary-scalar-result-domain build (car form)))
        ((and (consp form) (member (car form) '(list cons vector)))
         (values (if (some (lambda (part) (external-result-domain-p (value-domain build part))) (cdr form))
                     :external-result (if (eq (car form) 'vector) 'vector 'list)) t))
        ((and (consp form) (member (car form) '(car cdr first second third fourth fifth sixth seventh eighth
                                             ninth tenth rest nth nthcdr aref svref elt getf gethash values-list)))
         (values (if (some (lambda (part) (external-result-domain-p (value-domain build part))) (cdr form))
                     :external-result :unknown) t))
        ((and (consp form) (eq (car form) 'list*))
         ;; With one argument LIST* is identity, including nonlists.
         (let ((inputs (mapcar (lambda (part) (value-domain build part)) (cdr form))))
           (values (cond ((some #'external-result-domain-p inputs) :external-result)
                         ((and inputs (null (cdr inputs))) (car inputs))
                         ((cdr inputs) 'cons)
                         (t :unknown)) t)))
        ((and (consp form) (eq (car form) 'append))
         ;; APPEND returns its arbitrary final object when every prefix is
         ;; empty. A proved nonempty cons prefix guarantees a cons result on
         ;; successful return; otherwise include the final object's domain.
         (let ((inputs (mapcar (lambda (part) (value-domain build part)) (cdr form))))
           (values (cond ((some #'external-result-domain-p inputs) :external-result)
                         ((null inputs) '(eql nil))
                         ((null (cdr inputs)) (car inputs))
                         ((some (lambda (prefix) (subtype-domain-p build prefix 'cons)) (butlast inputs)) 'cons)
                         (t (merge-value-domains build 'cons (car (last inputs))))) t)))
        ((and (consp form) (member (car form) '(reverse remove delete))
              (standard-operation-meaning-p build (car form)))
         (values (native-sequence-result-domain
                  build (if (eq (car form) 'reverse) (second form) (third form))) t))
        ((and (consp form) (build-function-returns build)
              (member (car form) '(mapcar maplist mapcan reduce))
              (standard-operation-meaning-p build (car form)))
         (callback-operator-result-domain build (car form) (cdr form)))
        ((and (consp form) (eq (car form) 'coerce)
              (standard-operation-meaning-p build 'coerce))
         (coerce-result-domain build (cdr form)))
        ((and (consp form) (eq (car form) 'mapc)
              (standard-operation-meaning-p build 'mapc))
         ;; MAPC returns the first input list itself, not its callback results.
         ;; Preserve that object's origin; other input lists do not replace it.
         (values (value-domain build (third form)) t))
        ((and (consp form) (eq (car form) 'fill)
              (standard-operation-meaning-p build 'fill))
         ;; FILL returns its original sequence by identity. The value and
         ;; bounds affect mutation, not the returned sequence's provenance.
         (values (value-domain build (second form)) t))
        ((and (consp form) (eq (car form) 'make-instance))
         (values (source-construction-domain build form) t))
        ((and (consp form) (immediate-lambda-form build form))
         (values (return-summary-primary (immediate-lambda-return-summary build form)) t))
        ((and (consp form) (member (car form) '(funcall apply multiple-value-call)))
         (multiple-value-bind (targets global-targets callee-domain) (known-function-targets build (second form))
           (multiple-value-bind (ordinary precise-p)
               (ordinary-indirect-result-domain build form targets global-targets)
             (values (if precise-p ordinary
                         (return-summary-primary
                          (indirect-call-return-summary build form targets global-targets callee-domain)))
                     t))))
        ((and (consp form) (source-call-return-summary build (car form)))
         (values (return-summary-primary (source-call-return-summary build (car form))) t))
        (t :unknown)))

(defun subtype-domain-p (build actual expected)
  ;; Value selectors and sequence geometry do not impose identity. Project
  ;; them before distributing a union, so a shaped LIST|VECTOR still covers
  ;; that same union. Keep record qualifiers until expected-arm selection:
  ;; an OWNED alternative must match its OWNED arm rather than just its class.
  (when (relational-value-domain-p actual)
    (return-from subtype-domain-p (subtype-domain-p build (third actual) expected)))
  (when (relational-value-domain-p expected)
    (return-from subtype-domain-p (subtype-domain-p build actual (third expected))))
  (when (shaped-domain-p actual)
    (return-from subtype-domain-p (subtype-domain-p build (second actual) expected)))
  (when (and (consp actual) (eq (first actual) 'or))
    (return-from subtype-domain-p (every (lambda (part) (subtype-domain-p build part expected)) (rest actual))))
  (when (and (consp expected) (eq (first expected) 'or))
    (return-from subtype-domain-p (some (lambda (part) (subtype-domain-p build actual part)) (rest expected))))
  (cond ((initializing-record-domain-p expected)
         (and (initializing-record-domain-p actual) (eq (second actual) (second expected))))
        ((initializing-record-domain-p actual) (subtype-domain-p build (third actual) expected))
        ((owned-record-domain-p expected)
         (and (owned-record-domain-p actual) (name= (second actual) (second expected))))
        ((owned-record-domain-p actual) (subtype-domain-p build (second actual) expected))
        ((graph-node-domain-p expected)
         (and (graph-node-domain-p actual) (eql (second actual) (second expected))
              (subtype-domain-p build (third actual) (third expected))))
        ((graph-node-domain-p actual) (subtype-domain-p build (third actual) expected))
        ((shaped-domain-p actual) (subtype-domain-p build (second actual) expected))
        ((shaped-domain-p expected) (subtype-domain-p build actual (second expected)))
        ((eq expected t) t)
        ;; Internal fact markers are not host Common Lisp type specifiers.
        ((or (member actual '(:unknown :pending :external-result))
             (member expected '(:unknown :pending :external-result))) nil)
        ((and (consp actual) (eq (car actual) 'or))
         (every (lambda (alternative) (subtype-domain-p build alternative expected)) (cdr actual)))
        ((and (consp expected) (eq (car expected) 'or))
         (some (lambda (alternative) (subtype-domain-p build actual alternative)) (cdr expected)))
        ((or (external-value-domain-p build actual) (external-value-domain-p build expected))
         (equal actual expected))
        ((domain-function-target actual)
         (let ((name (domain-function-target actual)))
           (cond ((domain-function-target expected) (name= name (domain-function-target expected)))
                 ((and (consp expected) (eq (car expected) 'eql)) nil)
                 (t
               ;; Preserve source GF versus ordinary callable observations.
               ;; These disposable functions are queried only in the builder;
               ;; the persistent fact remains the qualified source name.
               (let ((function (cond ((or (member-name name (getf (build-declaration build) :closed-generics))
                                         (member-name name (build-functions build)))
                                      (let ((binding (mapped-name name (build-open-package build))))
                                        (when (fboundp binding) (fdefinition binding))))
                                     ((fboundp name) (fdefinition name)))))
                 (and function (typep function (if (member-name expected (build-classes build))
                                                 (mapped-name expected (build-open-package build)) expected))))))))
        ((domain-function-target expected) nil)
        ((and (consp actual) (eq (car actual) 'eql))
         (if (and (consp expected) (eq (car expected) 'eql))
             (eql (cadr actual) (cadr expected))
             (and (not (member-name expected (build-classes build))) (typep (cadr actual) expected))))
        ((and (consp expected) (eq (car expected) 'eql)) nil)
        (t (subtypep (if (member-name actual (build-classes build))
                        (mapped-name actual (build-open-package build)) actual)
                    (if (member-name expected (build-classes build))
                        (mapped-name expected (build-open-package build)) expected)))))

(defun domain-alternatives (domain)
  (if (and (consp domain) (eq (car domain) 'or)) (cdr domain) (list domain)))

(defun record-domain-p (build domain)
  (every (lambda (actual)
           (every (lambda (base) (member-name base (build-classes build)))
                  (domain-alternatives (private-record-domain-base actual))))
         (domain-alternatives domain)))

(defun builtin-type-test (build type value)
  ;; The physical output is a compiled ordinary function. Its source generic
  ;; was a funcallable CLOS object. Keep native built-in observations logical
  ;; for those exact finite callable identities; other values retain TYPEP.
  (let ((native `(typep ,value ',type))
        (ordinary (typep #'builtin-type-test type)))
    (dolist (name (getf (build-declaration build) :closed-generics) native)
      (let ((original (typep (open-generic build name) type)))
        (unless (eq (not (null original)) (not (null ordinary)))
          (setf native `(if (eq ,value #',(mapped-name name (build-output-package build)))
                           ,(not (null original)) ,native)))))))

(defun merge-value-domains (build previous additional)
  (when (or (relational-value-domain-p previous) (relational-value-domain-p additional))
    (return-from merge-value-domains
      (cond ((eq previous :pending) additional) ((eq additional :pending) previous)
            ((and (relational-value-domain-p previous) (relational-value-domain-p additional)
                  (equal (second previous) (second additional)))
             (list :relational-value (second previous)
                   (merge-value-domains build (third previous) (third additional))))
            (t (merge-value-domains build (relational-base previous) (relational-base additional))))))
  (cond ((eq previous :pending) additional)
        ((eq additional :pending) previous)
        ;; UNKNOWN must not erase the fact that a possible return came from
        ;; an opaque native boundary. Otherwise a join can authorize a closed
        ;; class observation of the actual original CLOS object.
        ((and (or (external-result-domain-p previous) (external-result-domain-p additional))
              (not (every #'graph-node-domain-p
                          (append (domain-alternatives previous) (domain-alternatives additional)))))
         (qualify-domain-origin
          (merge-value-domains build (value-domain-shape build previous)
                                    (value-domain-shape build additional))
          :external-result))
        ((or (eq previous :unknown) (eq additional :unknown)) :unknown)
        (t
         (let ((alternatives (remove-duplicates (append (domain-alternatives previous)
                                                       (domain-alternatives additional)) :test #'equal)))
           (setf alternatives
                 (remove-if (lambda (actual)
                              (some (lambda (other)
                                      (and (not (equal actual other))
                                           (subtype-domain-p build actual other)
                                           (or (not (subtype-domain-p build other actual))
                                               (string< (prin1-to-string other) (prin1-to-string actual)))))
                                    alternatives)) alternatives))
           (if (= (length alternatives) 1) (car alternatives)
               (cons 'or (sort alternatives #'string< :key #'prin1-to-string)))))))

(defun ordinary-function-form (build name)
  (when (and name (not (eq name :unknown)))
    (let ((definition (snowgrave:find-authored-definition (build-source build) :function name)))
      (when definition (normalized-definition-form build definition)))))

(defun call-lambda-domains (build lambda-list supplied variable-tail &key method specials lexical)
  "Project raw caller facts through the shared lambda binding owner."
  (let* ((contract (lambda-contract build lambda-list :method method))
         (inputs (lambda-input-variables contract)))
    (let ((*argument-domains* (when lexical *argument-domains*))
          (*function-bindings* (when lexical *function-bindings*))
          (*value-domain-local-functions* (when lexical *value-domain-local-functions*))
          (*local-function-frames* (when lexical *local-function-frames*)))
      (multiple-value-bind (key-inputs unknown-key-tail)
          (call-key-inputs contract supplied variable-tail)
        (multiple-value-bind (scope ordinary initializers)
            (analyze-lambda-scope build lambda-list supplied :call-inputs t :variable-tail variable-tail
                                  :method method :key-inputs key-inputs :unknown-key-tail unknown-key-tail
                                  :specials specials)
          (declare (ignore ordinary initializers))
          (values (mapcar (lambda (name) (cdr (assoc name (car scope)))) inputs)
                  (loop for name in inputs
                        for position = (position name (lambda-positional-variables contract))
                        collect (cond ((member name (getf contract :required)) :supplied)
                                      (position (cond ((< position (length supplied)) :supplied)
                                                      (variable-tail :maybe) (t :omitted)))
                                      ((member name (lambda-key-variables contract))
                                       (let* ((spec (nth (position name (lambda-key-variables contract)) (getf contract :keys)))
                                              (provided (assoc (keyword-name spec) key-inputs)))
                                         (cond (provided :supplied) (unknown-key-tail :maybe) (t :omitted))))
                                      (t :maybe)))))))))

(defun capture-lambda-domains (build lambda-list &key lexical specials)
  ;; Arbitrary future callers may omit OPTIONAL/KEY values. Unknown actual
  ;; inputs cannot erase an opaque default or a definition-site capture.
  (call-lambda-domains build lambda-list
                       (make-list (length (getf (lambda-contract build lambda-list) :required))
                                  :initial-element :unknown)
                       t :lexical lexical :specials specials))

(defun call-function-domains (build form arguments capture variable-tail)
  "Derive effective argument bindings through the shared lambda scope owner."
  (let ((lambda-list (caddr form)))
    (if capture (capture-lambda-domains build lambda-list :specials (body-special-domains (cdddr form)))
        (let ((supplied (mapcar (lambda (argument) (value-domain build argument)) arguments)))
          (audit-lambda-parser-inputs build (lambda-contract build lambda-list)
                                     supplied variable-tail (cadr form))
          (call-lambda-domains build lambda-list supplied variable-tail
                               :specials (body-special-domains (cdddr form)))))))

(defun audit-generic-call-shape (build name arguments capture variable-tail)
  (when (and *initialization-phase* *flow-defer-source-call* (not capture) (not *flow-deferred-call-p*))
    (return-from audit-generic-call-shape nil))
  ;; Raw argument counts are input facts, not multiple-value results. Keep
  ;; omission distinct from supplied NIL, and never pad them as result tuples.
  (when (and (build-generic-call-shapes build)
             (member-name name (getf (build-declaration build) :closed-generics)))
    (let* ((contract (lambda-contract build (sb-mop:generic-function-lambda-list (open-generic build name))))
           (required (length (getf contract :required)))
           (live (unless capture (mapcar (lambda (argument) (value-domain build argument)) arguments)))
           (actual (mapcar #'erase-initialization-domain live))
           (input (if (graph-state-profile-p build) (make-call-record-flow-input build live) actual))
           ;; Keep literal key names apart before joining their value domains.
           ;; Same-arity calls with different keys must not turn omission of a
           ;; method key into an unknown keyword tail. This also covers a
           ;; &REST generic whose congruent methods accept &KEY.
           (key (list (not (null capture))
                      (if (external-result-domain-p variable-tail) :external-result (not (null variable-tail)))
                      (length actual)
                      (mapcar (lambda (domain)
                                (when (and (consp domain) (eq (car domain) 'eql) (symbolp (second domain))) domain))
                              (nthcdr required actual))
                      ;; Native payload is distinct from sequence geometry.
                      ;; Keep each proof with its actual raw caller row; an
                      ;; unsafe same-arity caller must never inherit this bit.
                      (let ((positional (length (lambda-positional-variables contract))))
                        (when (and (not capture) (getf contract :optional)
                                   (not (getf contract :rest)) (not (getf contract :keyp))
                                   (> (length actual) positional))
                          (append (make-list positional)
                                  (mapcar (lambda (argument)
                                            (not (null (or (native-data-form-p build argument)
                                                           (graph-native-payload-form-p build argument)))))
                                          (nthcdr positional arguments)))))))
           (shapes (gethash name (build-generic-call-shapes build))))
      (audit-generic-minimum-arity build name required (length actual) capture)
      ;; Presence is also the deployment reachability fact. A call below
      ;; required arity still needs this generic's exact error implementation.
      (when (and (entry-rooted-deployment-p build) *collect-function-flow* (null shapes))
        (setf shapes (make-hash-table :test #'equal)
              (gethash name (build-generic-call-shapes build)) shapes
              *function-flow-changed* t))
      ;; Pending key names must not become a permanent unknown-name profile
      ;; when their helper return is discovered by a later iteration.
      ;; An unknown tail can supply required values too. Keep its short raw
      ;; prefix, rather than dropping that caller and borrowing another
      ;; caller's narrower required bindings.
      (when (or capture (and (or variable-tail (>= (length actual) required))
                             (not (member :pending (nthcdr required actual)))))
        (when (and *collect-function-flow* (null shapes))
          (setf shapes (make-hash-table :test #'equal)
                (gethash name (build-generic-call-shapes build)) shapes))
        (multiple-value-bind (previous presentp) (if shapes (gethash key shapes) (values nil nil))
         (cond (*collect-function-flow*
               (let ((merged (if presentp
                                 (if (graph-state-profile-p build) (join-record-flow-inputs build previous input)
                                     (mapcar (lambda (old new) (merge-value-domains build old new)) previous actual))
                                 input)))
                 (unless (and presentp (same-record-flow-input-p merged previous))
                   (setf (gethash key shapes) merged)
                   (setf *function-flow-changed* t))))
              ((or (not presentp)
                   (not (every (lambda (value expected)
                                 (flow-domain-covered-p build value expected))
                               actual (flow-input-domains previous))))
               (fail build 'snowgrave:incomplete-domain :generic-call-bindings
                     (format nil "Caller of ~S lacks its raw argument binding proof." name) :reachability))
              ((and (record-flow-input-p input) (record-flow-input-p previous)
                    (not (record-flow-input-covered-p build input previous)))
               (fail build 'snowgrave:incomplete-domain :generic-call-state
                     "A generic caller lacks the joined cell entry-state proof." :reachability))))))))

(defun intersect-method-cell-domain (build actual cell)
  ;; Return a binding fact and whether this caller can occupy the already
  ;; selected cell. UNKNOWN/captures cannot establish a private node identity.
  (cond ((relational-value-domain-p actual)
         (multiple-value-bind (selected possiblep) (intersect-method-cell-domain build (third actual) cell)
           (values (if possiblep (list :relational-value (second actual) selected) selected) possiblep)))
        ((eq actual :pending) (values :pending t))
        ((eq cell t) (values actual t))
        ((member actual '(:unknown :external-result)) (values cell t))
        (t (let ((selected :pending) (compatiblep nil))
             (dolist (part (domain-alternatives actual))
               (cond ((subtype-domain-p build part cell)
                      (setf selected (merge-value-domains build selected part) compatiblep t))
                     ;; A broad declared caller can occupy this class cell,
                     ;; but cannot lend it a particular graph node qualifier.
                     ((subtype-domain-p build cell (private-record-domain-base part))
                      (setf selected (merge-value-domains build selected cell) compatiblep t))))
             (values selected compatiblep)))))

(defun method-binding-domains (build generic lambda-list body)
  "Project whole compatible caller tuples through the existing MOP cell."
  (let* ((inputs (lambda-input-variables (lambda-contract build lambda-list :method t)))
         (required (length *cell-domains*))
         (summary nil) (state-summary nil)
         (shapes (gethash generic (build-generic-call-shapes build))))
    (when shapes
      (maphash
       (lambda (key input)
         (let ((domains (if (record-flow-input-p input) (record-flow-positional-inputs input) input)))
          (destructuring-bind (capture variable-tail count literal-names &optional native-payloads) key
           (declare (ignore literal-names native-payloads))
           (let ((supplied nil)
                 (compatiblep (or capture (initialization-generic-p generic)
                                  (not (configured-callable-retention-p build))
                                  (generic-call-row-possible-p build domains variable-tail count input))))
             (loop for cell in *cell-domains* for position from 0
                   do (multiple-value-bind (fact possiblep)
                          (if (or capture (initialization-generic-p generic)
                                  (and (not (graph-state-profile-p build)) (not (eq cell t))))
                              (values cell t)
                              (intersect-method-cell-domain build (if (< position count) (nth position domains) :unknown) cell))
                        (push fact supplied)
                        (unless possiblep (setf compatiblep nil))))
             (when compatiblep
               (let* ((actual (call-lambda-domains
                               build lambda-list (append (nreverse supplied) (unless capture (nthcdr required domains)))
                               (or capture variable-tail) :method t :specials (body-special-domains body)))
                      (row (if (record-flow-input-p input)
                               (project-record-flow-input build input actual)
                               (when (graph-state-profile-p build) (make-call-record-flow-input build actual)))))
                 (setf summary (if summary
                                   (mapcar (lambda (old new) (merge-value-domains build old new)) summary
                                           (mapcar #'relational-base actual))
                                   (mapcar #'relational-base actual)))
                 (when row (setf state-summary (if state-summary (join-record-flow-inputs build state-summary row) row))))))))) shapes))
    (let ((domains (or summary
                       (append (mapcar (lambda (cell)
                                         (if (and (graph-state-profile-p build) *collect-function-flow* (not *settled-method-roots*))
                                             :pending
                                             (if (or (not (eq cell t)) (initialization-generic-p generic))
                                                 cell (if (and *collect-function-flow* (not *settled-method-roots*)) :pending :unknown))))
                                       *cell-domains*)
                               (make-list (- (length inputs) required)
                                          :initial-element (if (and *collect-function-flow* (not *settled-method-roots*)) :pending :unknown))))))
      (values domains (or state-summary (when (graph-state-profile-p build) (make-call-record-flow-input build domains)))))))

(defun audit-function-call (build name arguments &key capture variable-tail)
  (when (and *initialization-phase* *flow-defer-source-call* (not capture) (not *flow-deferred-call-p*)
             (ordinary-function-form build name))
    (return-from audit-function-call nil))
  (when (build-function-domains build)
    (let ((form (ordinary-function-form build name)))
      (when form
        (let* ((required (ordinary-lambda-list build (caddr form)))
               (count (length required))
               (entryp (member-name name (getf (build-declaration build) :entries)))
               (projection (multiple-value-list (call-function-domains build form arguments capture variable-tail)))
               (live (first projection))
               (actual (mapcar #'erase-initialization-domain live))
               (input (if (graph-state-profile-p build) (make-call-record-flow-input build live (second projection)) actual)))
          ;; Declared entry domains remain the public guard, rather than a
          ;; joined helper profile. An internal opaque origin cannot borrow
          ;; that nominal contract for an unclassified native value.
          (when (and entryp (not capture) (some #'external-result-domain-p actual))
            (fail build 'snowgrave:unclosed-call :external-result-entry-argument
                  "An internal call cannot reinterpret an unclassified external result through an entry's nominal domain contract."
                  :reachability))
          ;; An ordinary lambda list rejects an incomplete tuple before its
          ;; body. An escaping helper capture has arbitrary future callers.
          (when (or capture (>= (length arguments) count))
            (multiple-value-bind (previous presentp) (gethash (cadr form) (build-function-domains build))
              (cond
                (*collect-function-flow*
                 (unless (or entryp (member :pending (subseq actual 0 count)))
                   (let ((merged (if presentp
                                     (if (graph-state-profile-p build) (join-record-flow-inputs build previous input)
                                         (mapcar (lambda (old new) (merge-value-domains build old new)) previous actual))
                                     input)))
                     (unless (and presentp (same-record-flow-input-p merged previous))
                       (setf (gethash (cadr form) (build-function-domains build)) merged
                             *function-flow-changed* t)))))
                ;; Captures of declared entries retain their entry guard.
                ((and capture entryp) nil)
                ((not presentp)
                 (fail build 'snowgrave:incomplete-domain :ordinary-function-reachability
                       (format nil "No caller-domain proof reaches ordinary helper ~S." name) :reachability))
                ((and capture
                      (not (every (lambda (value expected) (flow-domain-covered-p build value expected))
                                  actual (flow-input-domains previous))))
                 (fail build 'snowgrave:incomplete-domain :ordinary-function-capture-domain
                       (format nil "Escaping helper ~S lacks an arbitrary-caller proof." name) :reachability))
                ((and (not capture)
                      (not (every (lambda (value expected)
                                    (flow-domain-covered-p build value expected))
                                  actual (flow-input-domains previous))))
                 (fail build 'snowgrave:incomplete-domain :ordinary-function-call-domain
                       (format nil "Caller of ~S supplies ~S outside proved required domains ~S." name actual previous)
                       :reachability))
                ((and (record-flow-input-p input) (record-flow-input-p previous)
                      (not (record-flow-input-covered-p build input previous)))
                 (fail build 'snowgrave:incomplete-domain :ordinary-function-state
                       "A helper caller lacks its joined entry-state proof." :reachability))))))))))

(defun audit-function-capture (build name)
  (when (member name '(fill coerce length))
    (fail build 'snowgrave:unclosed-call :ordinary-function-capture
          "This ordinary operator needs a proved callable ABI before its unchecked host function can escape; use an audited immediate call."))
  (audit-generic-call-shape build name nil t nil)
  (audit-function-call build name nil :capture t))

(defun audit-place-writer (build place value local)
  (when (consp place)
    (let ((binding (find-local-function-binding (list 'setf (car place)))))
      (when binding
        (local-call-return-summary build binding
                                   (list* (local-function-binding-name binding) value (cdr place))))))
  (when (and (consp place) (not (member-name (list 'setf (car place)) local))
             (function-target-p build (list 'setf (car place)) local))
    (let ((name (list 'setf (car place))) (arguments (cons value (cdr place))))
      (audit-generic-call build name arguments)
      (audit-function-call build name arguments)
      (audit-external-call build name arguments))))

(defun generic-domain-roots (build generic)
  (when (initialization-generic-p generic)
    (return-from generic-domain-roots
      (append (list (copy-list (build-classes build)))
              (when (eq generic 'shared-initialize) (list (list t))))))
  (let* ((gf (open-generic build generic))
         (count (length (ordinary-lambda-list build (sb-mop:generic-function-lambda-list gf)))))
    (loop for position below count
          collect (remove-duplicates
                   (append (copy-list (getf (build-declaration build) :universe))
                    (mapcar (lambda (method)
                             (let ((specializer (nth position (sb-mop:method-specializers method))))
                               (if (typep specializer 'sb-mop:eql-specializer)
                                   (list 'eql (sb-mop:eql-specializer-object specializer))
                                   (source-class build specializer))))
                           (sb-mop:generic-function-methods gf))) :test #'equal))))

(defun audit-initialization-call (build name arguments)
  (when (and (initialization-generic-p name) (not *generated-class-operation*))
    (audit-initialization-state-inputs build name arguments)
    (let* ((required (if (eq name 'shared-initialize) 2 1))
           (keys (nthcdr required arguments)))
      (unless (and (>= (length arguments) required) (evenp (length keys))
                   (loop for tail on keys by #'cddr always (keywordp (car tail))))
        (fail build 'snowgrave:unclosed-class-operation :initialization-argument-shape
              "Direct initialization calls need a proven complete tuple and literal keyword names." :reachability))
      (when (eq name 'shared-initialize)
        (let* ((selection (second arguments))
               (value (if (and (consp selection) (eq (car selection) 'quote)) (cadr selection) selection)))
          (unless (or (eq value t) (null value)
                      (and (consp selection) (eq (car selection) 'quote)
                           (listp value) (every #'symbolp value)))
            (fail build 'snowgrave:unclosed-class-operation :slot-initform-selection
                  "SHARED-INITIALIZE needs T or a literal list of slot names in this fragment." :reachability)))))))

(defun audit-generic-call (build name arguments &key variable-tail)
  (audit-initialization-call build name arguments)
  (when (member-name name (getf (build-declaration build) :closed-generics))
    (when (and (not *collect-function-flow*)
               (or (external-result-domain-p variable-tail)
                   (some (lambda (argument) (external-result-domain-p (value-domain build argument))) arguments)))
      (fail build 'snowgrave:unclosed-call :external-result-dispatch
            "Closed dispatch needs an admitted representation for values returned by an external operation." :reachability))
    (audit-generic-call-shape build name arguments nil variable-tail)
    (let ((domains (generic-domain-roots build name)))
      ;; No tuple exists below required arity. The materialized host parser
      ;; signals before any applicability or domain observation can occur.
      (when (< (length arguments) (length domains))
        (return-from audit-generic-call t))
      (loop for argument in arguments for roots in domains for position from 0
            unless (or *collect-function-flow*
                       (every (lambda (actual)
                                (some (lambda (root) (subtype-domain-p build actual root)) roots))
                              (domain-alternatives (value-domain build argument))))
              do (fail build 'snowgrave:incomplete-domain :internal-call-domain
                       (format nil "Cannot prove argument ~D of ~S (~S) lies inside ~S."
                               position name argument roots) :reachability)))))

(defun audit-assignment-targets (build places)
  "Use the same mutation policy for single and multiple-value assignments."
  (dolist (place places)
    (when (and (symbolp place)
               (or (and (assoc place *argument-domains*) (not (member place (source-specials build)))
                        (not (admitted-mutation-p place)))
                   (and (special-variable-p build place) (captured-function build place))
                   (let ((target (resolved-function build place))) (and target (not (eq target :unknown))))))
      (fail build 'snowgrave:unsupported-definition :value-domain-mutation
            "Lexical argument mutation and mutable function captures need flow-sensitive proof."))
    (when (and (member place (source-specials build)) (assoc place *argument-domains*))
      (setf (cdr (assoc place *argument-domains*)) :unknown))))

(defun exact-class-comparison (build form local)
  "Recognize an ordinary exact-class observation without exposing a class value.
Only EQ of unary CLASS-OF and literal cohort FIND-CLASS is proved here. Other
reflection, lexical rebinding and class values still require their own ABI."
  (when (and (consp form) (eq (car form) 'eq) (= (length form) 3)
             (not (some (lambda (name)
                          (or (member-name name local) (member-name name (build-functions build))
                              (member-name name (getf (build-declaration build) :closed-generics))))
                        '(eq class-of find-class))))
    (let* ((reversep (and (consp (second form)) (eq (car (second form)) 'find-class)))
           (observation (if reversep (third form) (second form)))
           (lookup (if reversep (second form) (third form))))
      (when (and (consp observation) (eq (car observation) 'class-of) (= (length observation) 2)
                 (consp lookup) (eq (car lookup) 'find-class) (= (length lookup) 2))
        (multiple-value-bind (class constantp) (quoted-value (second lookup))
          (when (and constantp (member-name class (build-classes build)))
            (values (second observation) class reversep t)))))))

(defun transform-body (build body package &key open next original local immediate-result-p)
  (with-source-body-facts (body)
   (let ((*value-domain-local-functions* local)
         (*immediate-lambda-domains* *immediate-lambda-domains*)
         (last-summary (make-return-summary (list '(eql nil)) t)))
    (multiple-value-bind (prefix executable) (snowgrave::source-body-parts body)
      (labels ((emit (form &optional immediatep)
                 (let ((*immediate-callee-value* (when immediatep form)))
                   (multiple-value-bind (code summary)
                       (transform-form build form package :open open :next next :original original :local local)
                     (when summary (setf last-summary summary)) code))))
        (values
         (append (mapcar (lambda (form) (if (stringp form) form (emit form))) prefix)
                 (loop for tail on executable
                       collect (emit (car tail) (and immediate-result-p (null (cdr tail))))))
         last-summary))))))

(defun declared-external-result-expression (build name expression)
  (let ((contract (assoc name (getf (build-declaration build) :external-return-domains) :test #'name=)))
    (if (and contract (not *collect-function-flow*))
        `(the (values ,@(mapcar (lambda (domain) (external-result-native-type build domain)) (second contract)) &optional)
           ,expression) expression)))

(defun transform-form (build form package &key open next original local)
  (when (and open *cold-recipe-source-marker* (consp form)
             (eq (car form) *cold-recipe-source-marker*))
    (let ((*cold-recipe-active* t))
      (return-from transform-form
        (transform-form build (second form) package :open open :next next :original original :local local))))
  (when (and open *cold-recipe-active*) (audit-cold-recipe-form build form local))
  (when (and *effective-method-emitter* (consp form) (eq (first form) 'call-method))
    (multiple-value-bind (code summary) (funcall *effective-method-emitter* form package local)
      (let ((previous (assoc form *flow-value-receipts* :test #'eq)))
        (setf *flow-value-receipts*
              (acons form (if previous (merge-return-summaries build (cdr previous) summary) summary)
                     (remove form *flow-value-receipts* :key #'car :test #'eq))))
      (return-from transform-form (values code summary))))
  (flet ((emit ()
           (let ((code
                   (if (and *initialization-phase* (not open))
                       (let ((*flow-defer-source-call* (record-flow-owned-call-p build form)))
                         (transform-initialization-form
                          build form
                          (lambda () (transform-form-code build form package :open open :next next :original original :local local))))
                       (transform-form-code build form package :open open :next next :original original :local local))))
             ;; Child receipts preserve the final APPLY operand at its value
             ;; point, including earlier argument effects and PROG1 cleanup.
             (when (and (not open) (consp form) (eq (car form) 'apply))
               (audit-apply-parser-tail build form))
             code)))
    (if (and *initialization-phase* (not open))
        (call-with-transformed-value-receipt build form #'emit)
        (emit))))

(defun transform-form-code (build form package &key open next original local)
  (labels
      ((walk (x) (transform-form build x package :open open :next next
                                :original original :local local))
       (value-walk (x)
         (let ((*immediate-callee-value* (when (eq form *immediate-callee-value*) x)))
           (walk x)))
       (body (xs &optional resultp)
         (transform-body build xs package :open open :next next :original original :local local
                         :immediate-result-p (and resultp (eq form *immediate-callee-value*))))
       (target (name)
         (transformed-function-name build name package open local))
       (cem-source-call-p ()
         (and *effective-method-emitter*
              (or (find-local-function-binding (car form))
                  (ordinary-function-form build (car form))
                  (member-name (car form) (getf (build-declaration build) :closed-generics)))))
       (audit-source-call ()
         (when (find-local-function-binding (car form))
           (local-call-return-summary build (find-local-function-binding (car form)) form))
         (unless (member-name (car form) local)
           (audit-generic-call build (car form) (cdr form))
           (audit-function-call build (car form) (cdr form))
           (audit-external-call build (car form) (cdr form))))
       (equality-callback (reference operators &optional callee)
         (let ((callback (gensym "MAPPING-CALLBACK")))
           `(let ((,callback ,(walk reference)))
              (if ,(if callee
                       `(and (or ,@(mapcar (lambda (name) `(eq ,callee #',name)) operators))
                             (eq ,callback #'equalp))
                       `(eq ,callback #'equalp))
                  #'eq ,callback))))
       (equality-arguments (arguments plans &optional callee (start 0))
         (loop for argument in arguments for index from start
               for operators = (cdr (assoc index plans))
               collect (if operators (equality-callback argument operators callee) (walk argument))))
       (call-equality-arguments (call callee plans)
         ;; Change only the callback argument at its original evaluation point.
         ;; Preserve the actual APPLY list/VALUES producers and every effect;
         ;; neither tuple flattening nor a callback wrapper allocation occurs.
         (let ((arguments (cddr call)))
           (case (car call)
             (funcall (equality-arguments arguments plans callee))
             (apply
              (let* ((prefix (butlast arguments)) (tail (car (last arguments)))
                     (offset (length prefix)))
                (append (equality-arguments prefix plans callee)
                        (list (if (and (consp tail) (eq (car tail) 'list))
                                  `(list ,@(equality-arguments (cdr tail) plans callee offset))
                                  (walk tail))))))
             (multiple-value-call
              (let ((index 0))
                (mapcar (lambda (producer)
                          (prog1 `(values ,@(equality-arguments (cdr producer) plans callee index))
                            (incf index (length (cdr producer))))) arguments)))))))
    (cond
      ((symbolp form)
       (if (member form (build-globals build)) (global-binding-name build form package open) form))
      ((atom form)
       (when (and *effective-method-emitter* (not (serializable-tree-p form)))
         (fail build 'snowgrave:residual-metaobject :effective-method-constant
               "The MOP effective method contains a builder constant." :materialization))
       (if (arrayp form)
           (literal-reference build form package) form))
      ((eq (car form) 'quote)
       (unless (serializable-literal-graph-p (cadr form) (build-literal-states build))
         (fail build 'snowgrave:residual-metaobject
               (if *effective-method-emitter* :effective-method-quote :quoted-object)
               "Literal graphs need readable native scalar, cons and array nodes."))
       (if (or (consp (cadr form)) (arrayp (cadr form)))
           (literal-reference build (cadr form) package) form))
      ((eq (car form) 'function)
       (if (and (consp (cadr form)) (eq (caadr form) 'lambda))
           `(function ,(walk (cadr form)))
           (progn
             (let ((binding (find-local-function-binding (second form))))
               (unless (or open (eq form *immediate-callee-value*))
                 (if binding (audit-local-function-capture build binding)
                     (retain-named-callable build (second form)))))
             `(function ,(target (cadr form))))))
      ((eq (car form) 'declare)
       ;; Closed class type declarations must not enter the host compiler as
       ;; CLOS type assertions about the ordinary record representation.
       (when (some (lambda (spec) (and (consp spec)
                                     (or (member-name (car spec) (build-classes build))
                                         (and (eq (car spec) 'type)
                                              (member-name (cadr spec) (build-classes build))))))
                   (cdr form))
         (fail build 'snowgrave:unclosed-class-operation :class-type-declaration
               "Use a closed TYPEP check; class type declarations need a target representation mapping."))
       (unless open (audit-declaration-payloads build (cdr form)))
       form)
      ((eq (car form) 'call-next-method)
       (cond (open form)
             ((cdr form)
              (fail build 'snowgrave:unsupported-definition :changed-argument-next-method
                    "Changed-argument next methods need the host's exact continuation/error mapping."))
             (*initialization-next*
              (fail build 'snowgrave:unsupported-definition :initialization-continuation-context
                    "This lexical control/helper context has no transported initialization state proof." :reachability))
             (next `(,next ,@original))
             (*current-method*
              (emit-standard-miss build 'no-next-method
                                  (first *current-method*) (second *current-method*)
                                  (if *fixed-effective-arguments* (fixed-effective-error-arguments original) (car original))))
             (t (fail build 'snowgrave:mop-failure :no-next-method-context
                      "CALL-NEXT-METHOD has no reproducible authored method context." :materialization))))
      ((eq (car form) 'next-method-p)
       (if open form (if *current-method* (not (null (third *current-method*))) (not (null next)))))
      ((eq (car form) 'if)
       (let ((test (walk (cadr form))))
         (cond ((eq test t) (with-predicate-domains (build (second form) t local) (value-walk (third form))))
               ((null test) (with-predicate-domains (build (second form) nil local) (value-walk (fourth form))))
               (t (multiple-value-bind (yes no)
                      (call-with-initialization-branches
                       build (second form)
                       (lambda () (with-predicate-domains (build (second form) t local) (value-walk (third form))))
                       (lambda () (with-predicate-domains (build (second form) nil local) (value-walk (fourth form)))) local)
                    `(if ,test ,yes ,no))))))
      ((nth-value 3 (exact-class-comparison build form local))
       (multiple-value-bind (object class reversep) (exact-class-comparison build form local)
         (when (and (not open) (not *collect-function-flow*)
                    (external-result-domain-p (value-domain build object)))
           (fail build 'snowgrave:unclosed-call :external-result-class-observation
                 "Exact class comparison needs the external result's representation ABI." :reachability))
         (if open
             (let ((observation `(class-of ,(walk object)))
                   (lookup `(find-class ',(mapped-name class package))))
               `(eq ,@(if reversep (list lookup observation) (list observation lookup))))
             (progn
               (unless (or *collect-function-flow* (record-domain-p build (value-domain build object)))
                 (fail build 'snowgrave:unclosed-class-operation :exact-class-receiver
                       "Exact CLASS-OF comparison needs a sealed record receiver proof." :reachability))
               ;; Existing layout-owned tokens preserve exact class and unit
               ;; identity; ancestor TYPEP membership is deliberately different.
               (let ((observation `(snowgrave:sg-record-class ,(walk object)))
                     (token `',(getf (find class (build-layouts build)
                                          :key (lambda (layout) (getf layout :class)) :test #'name=)
                                    :class-token)))
                 `(eq ,@(if reversep (list token observation) (list observation token))))))))
      ((eq (car form) 'cond)
       `(cond ,@(mapcar (lambda (clause) (cons (walk (car clause))
                                         (with-predicate-domains (build (car clause) t local) (body (cdr clause)))))
                       (conditional-clauses build form))))
      ((member (car form) '(let let*))
       (multiple-value-bind (scope bindings)
           (analyze-let-scope build (cadr form) (eq (car form) 'let*) #'walk
                              :open open :specials (body-special-domains (cddr form)))
         (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
           `(,(car form)
             ,(mapcar (lambda (binding)
                        (list (if (member (first binding) (build-globals build))
                                  (global-binding-name build (first binding) package open) (first binding))
                              (second binding))) bindings)
             ,@(let ((specials (intersection (mapcar #'first bindings) (source-specials build))))
                 (when specials (list `(declare (special ,@specials)))))
             ,@(body (cddr form))))))
      ((member (car form) '(flet labels))
       (call-with-local-function-scope
        build form
        (lambda (frame)
          `(,(car form)
            ,(loop for binding in (local-function-frame-bindings frame)
                   when (or open (local-function-binding-reachedp binding))
                     collect
                     (call-in-local-function-environment
                      build frame t
                      (lambda ()
                        (let ((definition (local-function-binding-definition binding)))
                          (multiple-value-bind (scope ordinary)
                              (analyze-lambda-scope
                               build (second definition) (local-function-binding-domains binding)
                               :package package :open open :local *value-domain-local-functions*
                               :next next :original original :specials (body-special-domains (cddr definition)))
                            (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
                              (list* (first definition) ordinary
                                     (append (when (source-specials build)
                                               (list `(declare (special ,@(source-specials build)))))
                                             (transform-body build (cddr definition) package :open open
                                                             :next next :original original
                                                             :local *value-domain-local-functions*)))))))))
            ,@(transform-body build (cddr form) package :open open :next next :original original
                              :local *value-domain-local-functions*)))
        :package package :open open :next next :original original :local local))
      ((eq (car form) 'lambda)
       (multiple-value-bind (scope ordinary)
           (analyze-lambda-scope build (cadr form)
               (cdr (assoc form *immediate-lambda-domains*))
               :package package :open open :local local
                                :next next :original original
                                :specials (body-special-domains (cddr form)))
        (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
         `(lambda ,ordinary
            ,@(when (source-specials build) (list `(declare (special ,@(source-specials build)))))
            ,@(body (cddr form))))))
      ((eq (car form) 'tagbody)
       (let* ((targets (loop for part in (cdr form) when (atom part)
                             collect (cons part (gensym "LEXICAL-TAG"))))
              (*tagbody-targets* (append targets *tagbody-targets*)))
         `(tagbody ,@(mapcar (lambda (part)
                              (if (atom part) (cdr (assoc part targets :test #'eql)) (walk part)))
                            (cdr form)))))
      ((eq (car form) 'go)
       (let ((target (assoc (second form) *tagbody-targets* :test #'eql)))
         (unless target
           (fail build 'snowgrave:unsupported-definition :lexical-control
                 "GO needs an enclosing normalized TAGBODY target."))
         `(go ,(cdr target))))
      ((eq (car form) 'the)
       (unless (or (native-value-type-p (second form)) (member (second form) '(t list cons)))
         (fail build 'snowgrave:unclosed-class-operation :type-assertion
               "THE needs an admitted native type or explicit closed representation mapping."))
       (multiple-value-bind (code receipt) (walk (third form))
         ;; The child's saved value precedes its cleanup/other operand effects.
         ;; A fresh query of mutable state could authorize a different datum.
         (unless open
           (audit-private-type-input build (second form)
                                     (return-summary-primary
                                      (or receipt (flow-receipt-summary build (third form))))
                                     :private-type-assertion-error))
         `(the ,(second form) ,code)))
      ((member (car form) '(block return-from catch throw))
       (when (and (eq (car form) 'throw) (not open) (graph-state-profile-p build)
                  (not *collect-function-flow*))
         (audit-graph-native-inputs build (cdr form) :graph-state-throw))
       `(,(car form) ,(if (member (car form) '(catch throw))
                         (walk (cadr form)) (cadr form))
         ,@(body (cddr form))))
      ((member (car form) '(and or))
       (labels ((terms (arguments)
                  (when arguments
                    (let ((first (walk (car arguments))))
                      (if (null (cdr arguments)) (list first)
                          (multiple-value-bind (rest ignored)
                              (if (eq (car form) 'and)
                                  (call-with-initialization-branches
                                   build (car arguments)
                                   (lambda () (with-predicate-domains (build (car arguments) t local)
                                                (terms (cdr arguments))))
                                   (lambda () nil) local)
                                  (multiple-value-bind (yes no)
                                      (call-with-initialization-branches
                                       build (car arguments) (lambda () nil)
                                       (lambda () (with-predicate-domains (build (car arguments) nil local)
                                                    (terms (cdr arguments)))) local)
                                    (values no yes)))
                            (declare (ignore ignored)) (cons first rest)))))))
         `(,(car form) ,@(terms (cdr form)))))
      ((member (car form) '(when unless))
       (let ((test (walk (second form))))
         (multiple-value-bind (yes no)
             (call-with-initialization-branches
              build (second form)
              (lambda () (when (eq (car form) 'when)
                           (with-predicate-domains (build (second form) t local) (body (cddr form)))))
              (lambda () (when (eq (car form) 'unless)
                           (with-predicate-domains (build (second form) nil local) (body (cddr form))))) local)
           `(,(car form) ,test ,@(if (eq (car form) 'when) yes no)))))
      ((member (car form) '(progn locally))
       `(,(car form) ,@(body (cdr form) t)))
      ((eq (car form) 'multiple-value-prog1)
       (with-source-body-facts ((cdr form))
         `(multiple-value-prog1 ,(value-walk (second form))
            ,@(mapcar #'walk (cddr form)))))
      ((eq (car form) 'unwind-protect)
       (let ((protected (walk (second form))))
         ;; Cleanup also runs after a partially completed abrupt initializer.
         ;; Its audit cannot borrow only the successful protected poststate.
         (when *initialization-phase* (forget-initialization-state))
         `(unwind-protect ,protected ,@(body (cddr form)))))
      ((eq (car form) 'multiple-value-bind)
       (multiple-value-bind (scope value)
           (analyze-multiple-value-scope build (cadr form) (caddr form) #'walk
                                        :open open :specials (body-special-domains (cdddr form)))
         (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
           `(multiple-value-bind ,(cadr form) ,value
              ,@(when (source-specials build) (list `(declare (special ,@(source-specials build)))))
              ,@(body (cdddr form))))))
      ((eq (car form) 'destructuring-bind)
       (let ((value (walk (caddr form))))
        (with-destructuring-source-facts (build form)
         `(,(car form) ,(cadr form) ,value
            ,@(when (source-specials build) (list `(declare (special ,@(source-specials build)))))
            ,@(body (cdddr form))))))
      ((eq (car form) 'multiple-value-setq)
       (let ((variables (snowgrave:source-required-binding-variables
                         (cadr form) :source-key (build-source-key build) :path (list (build-identity build)))))
         (unless open (audit-assignment-targets build variables))
         `(multiple-value-setq
            ,(mapcar (lambda (variable) (transform-place build variable package open local)) variables)
            ,(walk (caddr form)))))
      ((member (car form) '(case ecase))
       (when (and (eq (car form) 'ecase) (not open) (not *collect-function-flow*)
                  (not (native-data-form-p build (cadr form))))
         (fail build 'snowgrave:unclosed-class-operation :ecase-error-datum
               "ECASE needs a native selector proof or an admitted logical condition-datum mapping." :reachability))
       `(,(car form) ,(walk (cadr form))
         ,@(mapcar (lambda (clause) (cons (car clause) (body (cdr clause))))
                   (case-clauses build form))))
      ((eq (car form) 'handler-case)
       `(handler-case ,(walk (cadr form))
          ,@(mapcar (lambda (clause)
                      (let ((*argument-domains* (append (mapcar (lambda (variable) (cons variable :unknown))
                                                               (handler-binding-variables build clause)) *argument-domains*))
                            (*function-bindings* (append (mapcar (lambda (variable) (cons variable :unknown))
                                                                (handler-binding-variables build clause)) *function-bindings*)))
                        (list* (car clause) (cadr clause)
                               (append (when (source-specials build)
                                         (list `(declare (special ,@(source-specials build)))))
                                       (body (cddr clause))))))
                    (cddr form))))
      ((eq (car form) 'handler-bind)
       `(handler-bind ,(mapcar (lambda (binding) (list (car binding) (walk (cadr binding))))
                               (cadr form)) ,@(body (cddr form))))
      ((and *cold-global-initializer* (eq (car form) 'make-symbol))
       ;; Keep allocation at its authored occurrence. Equal names do not
       ;; identify symbols, and no builder value becomes an emitted literal.
       (unless (fresh-symbol-initializer-p build form)
         (fail build 'snowgrave:nonreproducible-source :global-initializer
               "A cold MAKE-SYMBOL recipe requires one literal string name."))
       `(make-symbol ,(walk (second form))))
      ((eq (car form) 'load-time-value)
       (unless (reproducible-global-p build (cadr form))
         (fail build 'snowgrave:nonreproducible-source :load-time-capture
               "LOAD-TIME-VALUE must have a reproducible checked constant/function initializer."))
       `(load-time-value
          ,(let ((*argument-domains* nil) (*function-bindings* nil)
                 (*declared-specials* nil) (*value-domain-local-functions* nil) (*local-function-frames* nil)
               (*immediate-lambda-domains* nil)
                 (*mutable-invariant-bindings* nil) (*tagbody-targets* nil)
                 (*current-method* nil) (*cold-global-initializer* nil)
                 (*immediate-callee-value* (when (eq form *immediate-callee-value*) (second form))))
             (transform-form build (cadr form) package :open open))
          ,@(cddr form)))
      ((member (car form) '(funcall apply multiple-value-call))
       (let ((*immediate-lambda-domains* *immediate-lambda-domains*))
       (multiple-value-bind (targets global-targets) (unless open (known-function-targets build (second form)))
         (when (special-variable-p build (cadr form))
           (fail build 'snowgrave:unclosed-call :mutable-function-special
                 "A callable special needs a sealed binding-domain proof; use a lexical or direct LOAD-TIME-VALUE capture in this fragment."))
         (unless (or open *collect-function-flow*
                     (and (consp (cadr form))
                          (or (member (caadr form) '(function lambda))
                              (and (eq (caadr form) 'load-time-value)
                                   (not (eq (function-expression-target (cadr form)) :unknown)))))
                     targets)
           (fail build 'snowgrave:unclosed-call :computed-function
                 "Indirect calls require a checked FUNCTION/LAMBDA, immutable capture, or a complete finite set of named source targets."))
         (let ((equality-realization nil) (mapping-plans nil)
               (value-arguments nil) (value-bindings nil) (value-count-complete-p t)
               (*argument-domains* *argument-domains*))
         (when (and (not open) (eq (car form) 'multiple-value-call)
                    (not (every (lambda (producer) (and (consp producer) (eq (car producer) 'values))) (cddr form)))
                    (some (lambda (name) (indirect-argument-audit-p build name local global-targets))
                          targets))
           (multiple-value-bind (arguments bindings domains completep)
               (multiple-value-call-plan build (cddr form))
             (setf value-arguments arguments value-bindings bindings value-count-complete-p completep
                   *argument-domains* (append domains *argument-domains*))
             (unless (or completep *collect-function-flow*)
               (fail build 'snowgrave:incomplete-domain :multiple-value-arguments
                     "A multiple-value producer needs an exact ordered value-count/domain contract." :reachability))))
         (unless open
           (dolist (name targets)
            (if (local-function-binding-p name)
               (local-call-return-summary build name form)
               (let ((arguments (cddr form)) (variable-tail nil))
             ;; A returned global GF retains its source identity even inside a
             ;; same-named FLET. Local-name membership cannot waive its tuple.
             (when (and value-count-complete-p (indirect-argument-audit-p build name local global-targets))
               (when (eq (car form) 'apply)
                 (let ((required (if (ordinary-function-form build name)
                                     (length (ordinary-lambda-list build (caddr (ordinary-function-form build name))))
                                     (if (or (member name '(eq eql equal equalp))
                                             (member name *representation-sensitive-ordinary-operations*)
                                             (member-name name (getf (build-declaration build) :external-operations)))
                                         (length (ordinary-lambda-list build (sb-introspect:function-lambda-list (fdefinition name))))
                                         (length (generic-domain-roots build name))))))
                   ;; The same tuple owner used by flow and receiver emission
                   ;; distinguishes actual NIL/(LIST) tails from unknown tails.
                   (multiple-value-bind (tuple bindings completep tail-domain)
                       (ordinary-call-argument-plan build form :required-count required)
                     (declare (ignore bindings))
                     (unless completep
                       (fail build 'snowgrave:incomplete-domain :apply-arguments
                             "A variable APPLY tail cannot prove that every execution supplies the required tuple." :reachability))
                     (when (and tail-domain (initialization-generic-p name) (not *generated-class-operation*))
                       (fail build 'snowgrave:unclosed-class-operation :initialization-apply-tail
                             "A variable initialization APPLY tail needs a proven keyword/error shape." :reachability))
                     (setf arguments tuple variable-tail tail-domain))))
               (when (eq (car form) 'multiple-value-call)
                 (setf arguments
                       (if value-bindings value-arguments
                           (mapcan (lambda (producer) (copy-list (cdr producer))) arguments))))
               (audit-generic-call build name arguments :variable-tail variable-tail)
               (audit-function-call build name arguments :variable-tail variable-tail)
               (audit-external-identity build name arguments :variable-tail variable-tail)
               (audit-external-call build name arguments :variable-tail variable-tail)
               (dolist (position (audit-ordinary-operation build name arguments local open :variable-tail variable-tail))
                 (let ((plan (assoc position mapping-plans)))
                   (if plan (pushnew name (cdr plan)) (push (list position name) mapping-plans))))
               (when (eq name 'equalp)
                 (setf equality-realization
                       (record-equality-realization build arguments :variable-tail variable-tail))))))))
         (let ((native-sequence-position
                 (and (not open) (not *collect-function-flow*) (= (length targets) 1)
                      (native-sequence-argument-position (first targets))))
               (callee (let ((*immediate-callee-value* (second form))
                             (*immediate-lambda-domains*
                               (let ((lambda (immediate-lambda-form build form)))
                                 (if (and lambda (not open))
                                     (multiple-value-bind (domains completep)
                                         (immediate-lambda-call-domains build form)
                                       (if completep (acons lambda domains *immediate-lambda-domains*)
                                           *immediate-lambda-domains*))
                                     *immediate-lambda-domains*))))
                         (walk (cadr form)))))
           (cond (value-bindings
                  (let* ((binding (gensym "VALUE-CALLEE"))
                         (arguments (mapcan (lambda (producer) (copy-list (first producer))) value-bindings))
                         (invocation
                           (or (and (not open) (not equality-realization) (not mapping-plans)
                                    (emit-fixed-generic-invocation build binding arguments targets global-targets))
                               `(funcall ,(if (eq equality-realization :identity)
                                              `(if (eq ,binding #'equalp) #'eq ,binding) binding)
                                         ,@(cond (native-sequence-position
                                                  (asserted-sequence-arguments
                                                   build value-arguments
                                                   (if mapping-plans (equality-arguments arguments mapping-plans binding) arguments)
                                                   native-sequence-position))
                                                 (mapping-plans (equality-arguments arguments mapping-plans binding))
                                                 (t arguments))))))
                    `(let ((,binding ,callee))
                       ,(reduce (lambda (body producer)
                                  `(multiple-value-bind ,(first producer) ,(walk (second producer)) ,body))
                                (reverse value-bindings) :initial-value invocation))))
                 ((or (eq equality-realization :identity) mapping-plans)
               ;; Preserve the original callee's identity and evaluation, including
               ;; finite sets containing other functions. Only this invocation's
               ;; actual native EQUALP target changes to the record identity rule.
               (let ((binding (gensym "EQUALITY-CALLEE")))
                 `(let ((,binding ,callee))
                    (,(car form) ,(if (eq equality-realization :identity)
                                      `(if (eq ,binding #'equalp) #'eq ,binding) binding)
                     ,@(let ((arguments (if mapping-plans (call-equality-arguments form binding mapping-plans)
                                            (body (cddr form)))))
                         (if native-sequence-position
                             (native-sequence-indirect-arguments build form arguments native-sequence-position)
                             arguments))))))
                 (t (multiple-value-bind (tuple tuple-bindings completep variable-tail)
                        (fixed-invocation-argument-plan build form)
                      (let* (;; The ordinary tuple owner is also used by the
                             ;; audits. Generated MVC bindings are handled by
                             ;; the branch above; unknown tails stay ordinary.
                            (fixedp (and (not open) completep (null tuple-bindings) (null variable-tail)
                                         (some (lambda (target)
                                                 (and (not (local-function-binding-p target))
                                                      (member-name target global-targets)
                                                      (multiple-value-bind (minimum maximum) (fixed-generic-arity build target)
                                                        (and minimum (<= minimum (length tuple) maximum))))) targets)))
                            (expression
                              (or (when fixedp
                                    (emit-fixed-generic-invocation build callee (body tuple) targets global-targets))
                                  `(,(car form) ,callee
                                    ,@(let ((arguments (body (cddr form))))
                                        (if native-sequence-position
                                            (native-sequence-indirect-arguments build form arguments native-sequence-position)
                                            arguments))))))
                      (if (and (not open) (= (length targets) 1))
                          (declared-external-result-expression build (first targets) expression) expression))))))))))
      ((member (car form) '(setq setf incf decf push pushnew pop))
       (when (eq (car form) 'pushnew) (validate-keyword-callbacks build (cdddr form) local open nil
                                                                            :data (list (second form) (third form))))
       (unless open
         (let ((places (if (member (car form) '(setq setf))
                           (loop for tail on (cdr form) by #'cddr collect (car tail))
                           (if (member (car form) '(push pushnew)) (list (caddr form)) (list (cadr form))))))
           (audit-assignment-targets build places)))
       (when (and (not open) (member (car form) '(setq setf))
                  (not (and *initialization-phase* (eq (car form) 'setf))))
         (loop for (place value) on (cdr form) by #'cddr
               do (audit-external-place-value build place value)))
       (case (car form)
         (setf
          `(setf ,@(loop for (place value) on (cdr form) by #'cddr
                        append (progn
                                 (unless open (audit-missing-slot-writer build place value))
                                 (unless open (audit-place-writer build place value local))
                                 (let* ((location (transform-place build place package open local))
                                        (receiver (when (and *initialization-phase* (consp place)
                                                             (eq (first place) 'slot-value))
                                                    (value-domain build (second place))))
                                        (checked (when (and (not open) *initialization-phase*)
                                                   (audit-external-place-value build place value)))
                                        (value-code (walk value))
                                        (domain (when *initialization-phase* (value-domain build value))))
                                   (declare (ignore checked))
                                   (when (and *initialization-phase* (not open))
                                     (audit-external-place-value build place value))
                                   (note-initialization-place-write build place domain receiver local)
                                   (list location value-code))))))
         ((incf decf pop)
          (let* ((place (second form))
                 (location (transform-place build place package open local :readp t))
                 ;; SBCL evaluates the numeric delta before the old getter.
                 ;; Child receipts preserve the delta's actual returned value.
                 (operands (body (cddr form))))
            (unless open
              (let ((old-domain (audit-place-reader build place local)))
                (audit-graph-update-payload
                 build old-domain (and (symbolp place) (binding-native-payload-p place))))
              (dolist (operand (cddr form))
                (audit-graph-update-payload build (value-domain build operand)
                                            (graph-native-payload-form-p build operand)))
              (audit-place-writer build place (if (eq (car form) 'pop) '(cdr nil) '(+ 0)) local))
            `(,(car form) ,location ,@operands)))
         ((push pushnew)
          (let* ((item (walk (second form)))
                 (item-domain (value-domain build (second form)))
                 (native-item-p (and (symbolp (second form)) (binding-native-payload-p (second form))))
                 (place (third form))
                 (location (transform-place build place package open local :readp t))
                 ;; The old getter precedes PUSHNEW's keyword operands. Do
                 ;; not reconstruct it after a keyword form has changed state.
                 (old-domain (if open (value-domain build place) (audit-place-reader build place local)))
                 (native-old-p (and (symbolp place) (binding-native-payload-p place)))
                 (keywords (body (cdddr form))))
            (unless open
              (audit-graph-update-payload build item-domain native-item-p)
              (audit-graph-update-payload build old-domain native-old-p)
              (audit-external-place-value build place (second form))
              (audit-place-writer build place '(cons nil nil) local))
            `(,(car form) ,item ,location ,@keywords)))
         (otherwise `(,(car form) ,@(body (cdr form))))))
      ((member (car form) '(slot-value slot-boundp slot-makunbound))
       (when (and open (entry-rooted-deployment-p build))
         ;; Disposable CLOS uses the actual host slot protocol, including a
         ;; dynamic name and its error behavior. Closed records still need
         ;; the finite success/error proof below.
         (return-from transform-form-code `(,(car form) ,@(body (cdr form)))))
       (multiple-value-bind (slot constantp) (quoted-value (caddr form))
         (unless constantp
           (fail build 'snowgrave:unclosed-class-operation :dynamic-slot
                 "A dynamic slot name needs a finite success/error dispatcher."))
         (unless open
           (validate-record-slot build (cadr form) slot)
           (audit-graph-record-slot build (second form) (third form) :bound (eq (first form) 'slot-value)))
         (if open `(,(car form) ,(walk (cadr form)) ',slot)
             (case (car form)
               (slot-value `(snowgrave::%record-read ,(walk (cadr form)) ',slot
                                ',(mapcar (lambda (layout) (getf layout :class))
                                           (validate-record-slot build (cadr form) slot))))
               (slot-boundp `(snowgrave::%record-boundp ,(walk (cadr form)) ',slot
                                  ',(mapcar (lambda (layout) (getf layout :class))
                                             (validate-record-slot build (cadr form) slot))))
               (slot-makunbound
                (let ((record (fresh-name build "RECORD")))
                  `(let ((,record ,(walk (cadr form))))
                     (snowgrave::%record-unbind ,record ',slot
                       ',(mapcar (lambda (layout) (getf layout :class))
                                  (validate-record-slot build (cadr form) slot))) ,record)))))))
      ((and (eq (car form) 'typep) (standard-operation-meaning-p build 'typep local))
       (unless (member (length form) '(3 4))
         (fail build 'snowgrave:unclosed-class-operation :typep-arity
               "TYPEP needs two arguments and at most one environment argument."))
       (when (and (= (length form) 4)
                  (not (equal (value-domain build (fourth form)) '(eql nil))))
         (fail build 'snowgrave:unclosed-class-operation :type-environment
               "A non-null TYPEP environment needs a lexical environment/type expansion binding proof."))
       (multiple-value-bind (type constantp) (quoted-value (caddr form))
         (unless constantp
           (fail build 'snowgrave:unclosed-class-operation :dynamic-type
                 "A dynamic type requires an exact finite lowering."))
         (when (and (not open) (not *collect-function-flow*)
                    (member-name type (build-classes build))
                    (external-result-domain-p (value-domain build (cadr form))))
           (fail build 'snowgrave:unclosed-call :external-result-class-observation
                 "TYPEP cannot reinterpret an unclassified native external result as a lowered cohort instance." :reachability))
         (when (and (not open) (not *collect-function-flow*)
                    (member-name type (build-classes build))
                    (external-value-observation-p build (value-domain build (cadr form))))
           (fail build 'snowgrave:unclosed-call :external-value-class-observation
                 "An unchanged imported value has no cohort class/layout interpretation merely from its owner key." :reachability))
         (unless (or (member-name type (build-classes build)) (native-value-type-p type)
                     (and (symbolp type) (or (member type '(t function compiled-function list))
                                            (typep (find-class type nil) 'built-in-class))))
           (fail build 'snowgrave:unclosed-class-operation :type-observation
                 "Compound types and noncohort CLOS/structure classes need an exact record type lowering."))
         (if open `(typep ,(walk (cadr form)) ',(if (member-name type (build-classes build)) (mapped-name type package) type)
                         ,@(when (= (length form) 4) (list (walk (fourth form)))))
             (let ((value (fresh-name build "TYPE-VALUE"))
                   (environment (when (= (length form) 4) (fresh-name build "TYPE-ENVIRONMENT"))))
               `(let* ((,value ,(walk (cadr form)))
                       ,@(when environment `((,environment ,(walk (fourth form))))))
                  ,@(when environment `((declare (ignore ,environment))))
                  ,(if (member-name type (build-classes build))
                       (record-type-test build type value) (builtin-type-test build type value)))))))
      ((eq (car form) 'make-instance)
       (when (and open (entry-rooted-deployment-p build))
         ;; Class designators are evaluated once and sealed symbolic names
         ;; refer to their builder classes. Initargs keep normal host order.
         (return-from transform-form-code
           `(make-instance ,(open-class-name-expression build (cadr form) package local)
                           ,@(body (cddr form)))))
       (multiple-value-bind (class constantp) (quoted-value (cadr form))
         (unless (and constantp (member-name class (build-classes build)))
           (fail build 'snowgrave:unclosed-class-operation :dynamic-construction-class
                 "A construction site must name one sealed class."))
         (unless (and (evenp (length (cddr form)))
                      (loop for tail on (cddr form) by #'cddr always (keywordp (car tail))))
           (fail build 'snowgrave:unclosed-class-operation :construction-initargs
                 "Constructor sites need literal keyword names with a proven argument shape."))
         (unless open (source-construction-domain build form))
         (when (and (not open) (not *collect-function-flow*) (not (graph-state-profile-p build))
                    (loop for (key value) on (cddr form) by #'cddr
                          thereis (external-result-domain-p (value-domain build value))))
           (fail build 'snowgrave:unclosed-call :external-result-state
                 "Closed construction cannot retain an unclassified native external result without its value ABI." :reachability))
         (if open
             `(make-instance ',(mapped-name class package)
                ,@(loop for (key value) on (cddr form) by #'cddr append (list key (walk value))))
             `(,(ensure-constructor build class)
                ,@(loop for (key value) on (cddr form) by #'cddr append (list key (walk value)))))))
      ((member (car form) '(class-of find-class change-class
                            slot-missing slot-unbound))
       (if (and open (or (entry-rooted-deployment-p build) *cold-method-combination-factory*))
           (open-reflection-form build form package local)
           (fail build 'snowgrave:unclosed-class-operation (car form)
                 "This class operation requires construction/reflection/error protocol lowering.")))
      ((symbolp (car form))
       (unless (or open (member-name (car form) local))
         (audit-external-identity build (car form) (cdr form)))
       (let ((mapping-realization (audit-ordinary-operation build (car form) (cdr form) local open)))
         (when (and (not open) (not *collect-function-flow*) (eq (car form) 'equalp) (build-classes build))
           (when (eq :identity (record-equality-realization build (cdr form)))
             (return-from transform-form-code `(eq ,@(body (cdr form))))))
         (when (and (not open) (not (cem-source-call-p))) (audit-source-call))
         (cond
           ((and (eq (car form) 'coerce) (not open) (not *collect-function-flow*)
                 (standard-operation-meaning-p build 'coerce local))
            `(coerce ,(asserted-sequence-expression build (second form) (walk (second form)))
                     ,(walk (third form))))
           ((and (native-sequence-argument-position (car form)) (not open) (not *collect-function-flow*)
                 (standard-operation-meaning-p build (car form) local))
            `(,(car form) ,@(asserted-sequence-arguments
                            build (cdr form)
                            (if mapping-realization
                                (equality-arguments (cdr form)
                                                    (mapcar (lambda (position) (list position (car form))) mapping-realization))
                                (body (cdr form)))
                            (native-sequence-argument-position (car form)))))
           (mapping-realization
             `(,(target (car form))
                ,@(equality-arguments (cdr form)
                                     (mapcar (lambda (position) (list position (car form))) mapping-realization))))
           (t (multiple-value-bind (callee fixedp suffix)
                 (direct-call-name build (car form) package open local (length (cdr form)))
               (declare (ignore fixedp))
               (let ((expression `(,callee ,@(body (cdr form)) ,@suffix)))
                 ;; A composer leaf produces its typed value while walking
                 ;; the argument. Feed the same ordinary/local caller owner
                 ;; after those receipts exist, rather than permanently join
                 ;; the pre-evaluation opaque placeholder into helper inputs.
                 (when (and (not open) (cem-source-call-p)) (audit-source-call))
                 (if (or open (member-name (car form) local)) expression
                     (declared-external-result-expression build (car form) expression))))))))
      (t (fail build 'snowgrave:unsupported-definition :computed-operator
               "Computed operator forms are not in the audited source fragment.")))))

(defun audit-place-reader (build place local)
  "Audit one getter at its actual macro read point; emit no extra read."
  (when (consp place)
    (cond ((eq (car place) 'slot-value)
           (audit-graph-record-slot build (second place) (third place) :bound t))
          ((member (car place) '(getf gethash aref svref sbit bit car cdr))
           (audit-ordinary-operation build (car place) (cdr place) local nil))
          ((not (member-name (car place) local))
           (audit-generic-call build (car place) (cdr place))
           (audit-function-call build (car place) (cdr place))
           (audit-external-call build (car place) (cdr place)))))
  (if (and *initialization-phase* (record-flow-owned-call-p build place))
      ;; Getter effects occur before the writer. Use the same call receipt
      ;; owner as ordinary calls; do not borrow the pre-getter state row.
      (return-summary-primary (record-flow-call-receipt build place))
      (value-domain build place)))

(defun transform-place (build place package open local &key readp)
  (cond ((symbolp place)
         (if (member place (build-globals build)) (global-binding-name build place package open) place))
        ((and (consp place) (eq (car place) 'slot-value))
         (when (and open (entry-rooted-deployment-p build))
           (return-from transform-place
             `(slot-value ,@(transform-body build (cdr place) package :open t :local local))))
         (multiple-value-bind (slot constantp) (quoted-value (caddr place))
           (unless constantp
             (fail build 'snowgrave:unclosed-class-operation :dynamic-slot-writer
                   "A slot writer needs a constant effective slot or a finite success/error dispatcher."))
           (unless open (validate-record-slot build (cadr place) slot))
           `(,(if open 'slot-value 'snowgrave::%record-read)
             ,(transform-form build (cadr place) package :open open :local local) ',slot
             ,@(unless open
                 `(',(mapcar (lambda (layout) (getf layout :class))
                             (validate-record-slot build (cadr place) slot)))))))
        ((and (consp place) (member (car place) '(getf gethash aref svref sbit bit car cdr)))
         (when (and (not open) (eq (car place) 'gethash))
           (validate-hash-access build (cadr place) (caddr place)))
         (cons (car place) (transform-body build (cdr place) package :open open :local local)))
        ((and (consp place) (function-target-p build (list 'setf (car place)) local))
         (multiple-value-bind (callee fixedp suffix)
             (direct-call-name build (list 'setf (car place)) package open local (length place))
           ;; Read/modify/write needs BOTH conventions to agree. An unrelated
           ;; rest/key writer must never be redirected merely because its
           ;; reader has a fixed contract (or the converse).
           (when (and fixedp readp
                      (multiple-value-bind (minimum maximum) (fixed-generic-arity build (car place))
                        ;; Read/modify/write shares place subforms between the
                        ;; two functions. Optional transport counts differ by
                        ;; the inserted new value, so keep its ordinary path.
                        (not (and minimum (= minimum maximum (length (cdr place)))
                                  (= (length suffix) 1)))))
             (setf fixedp nil suffix nil
                   callee (transformed-function-name build (list 'setf (car place)) package open local)))
           (cons (second callee)
                 (append (transform-body build (cdr place) package :open open :local local)
                         suffix))))
        (t (fail build 'snowgrave:unclosed-call :setf-place
                 (format nil "No declared finite SETF operation for ~S." place)))))

(defun serializable-tree-p (value &optional (states (make-hash-table :test #'eq)))
  "Admit acyclic readable native data graphs; visit shared payload only once.
Simple T vectors use the same constant mechanism as scalars and conses. No
class, function, displaced backing or arbitrary array is hidden by this test."
  (labels ((walk (x)
               (cond ((symbolp x) (not (null (symbol-package x))))
                     ((or (numberp x) (characterp x) (stringp x)) t)
                     ((or (consp x) (simple-vector-p x))
                      (case (gethash x states)
                        (:complete t)
                        (:visiting nil)
                        (otherwise
                         (setf (gethash x states) :visiting)
                         (when (if (consp x) (and (walk (car x)) (walk (cdr x)))
                                   (loop for part across x always (walk part)))
                           (setf (gethash x states) :complete)
                           t))))
                     (t nil))))
    (walk value)))

(defun serializable-literal-graph-p (value &optional (states (make-hash-table :test #'eq)))
  "Validate a finite readable native graph, including shared and cyclic edges.
Only a complete successful traversal publishes memoized facts. Stable names,
declarations and compiler receipts keep their separate acyclic tree grammar."
  (let ((seen (make-hash-table :test #'eq)) (displacements (make-hash-table :test #'eq))
        (nodes nil) (pending (list value)))
    (loop while pending for part = (pop pending) do
      (cond ((symbolp part)
             (unless (symbol-package part) (return-from serializable-literal-graph-p nil)))
            ((or (numberp part) (characterp part)))
            ((or (consp part) (arrayp part))
             (unless (or (eq (gethash part states) :complete) (gethash part seen))
               (when (and (arrayp part)
                          (not (snowgrave::acyclic-array-displacement-p part displacements)))
                 (return-from serializable-literal-graph-p nil))
               (when (and (arrayp part)
                          (not (let ((type (array-element-type part)))
                                 (or (member type '(t nil bit)) (native-value-type-p type)
                                     (and (consp type) (eq (car type) 'complex)
                                          (= (length type) 2)
                                          (member (second type) '(single-float double-float short-float long-float)))))))
                 (return-from serializable-literal-graph-p nil))
               (setf (gethash part seen) t)
               (push part nodes)
               (if (consp part)
                   (progn (push (cdr part) pending) (push (car part) pending))
                   (multiple-value-bind (parent offset) (array-displacement part)
                     (declare (ignore offset))
                     (if parent (push parent pending)
                         (unless (null (array-element-type part))
                           (dotimes (index (array-total-size part))
                             (push (row-major-aref part index) pending))))))))
            (t (return-from serializable-literal-graph-p nil))))
    (dolist (node nodes) (setf (gethash node states) :complete))
    t))

(defun fresh-name (build role)
  (loop for name = (format nil "%~A/~D" role (incf (build-sequence build)))
        unless (some (lambda (source) (string= name (source-name source)))
                     (append (build-functions build) (build-generics build)
                             (build-globals build) (build-classes build)))
          return (intern name (build-output-package build))))

(defun ordinary-lambda-list (build list &key method)
  (getf (lambda-contract build list :method method) :required))

(defun lambda-contract (build lambda-list &key method)
  (snowgrave:source-lambda-contract lambda-list :specialized-required-p method :source-key (build-source-key build)
                                  :path (list (build-identity build))))

(defun lambda-positional-variables (contract)
  (append (getf contract :required)
          (mapcar (lambda (binding) (if (consp binding) (car binding) binding)) (getf contract :optional))))

(defun lambda-key-variables (contract)
  (mapcar (lambda (binding)
            (let ((head (if (consp binding) (car binding) binding)))
              (if (consp head) (second head) head)))
          (getf contract :keys)))

(defun lambda-input-variables (contract)
  ;; The existing caller fixed point owns REST contents as well as named
  ;; parameters. LIST shape alone cannot erase an opaque actual element.
  (append (lambda-positional-variables contract) (lambda-key-variables contract)
          (when (getf contract :rest) (list (getf contract :rest)))))

(defun call-key-inputs (contract supplied variable-tail)
  "Project known first-occurrence keyword inputs from already summarized facts.
The ordinary emitted lambda list still owns parsing, errors and default effects.
An unknown name makes that name and the remainder uncertain, never absent."
  (let ((tail (nthcdr (min (length supplied) (length (lambda-positional-variables contract))) supplied))
        (inputs nil))
    (loop while (cdr tail) do
      (let ((name-domain (car tail)))
        (unless (and (consp name-domain) (eq (car name-domain) 'eql) (symbolp (second name-domain)))
          (return-from call-key-inputs
            (values inputs (if (or (external-result-domain-p variable-tail)
                                   (some #'external-result-domain-p tail))
                               :external-result t))))
        (unless (assoc (second name-domain) inputs)
          (push (cons (second name-domain) (second tail)) inputs)))
      (setf tail (cddr tail)))
    (values inputs (if (or (external-result-domain-p variable-tail)
                          (some #'external-result-domain-p tail))
                      :external-result (or variable-tail (not (null tail)))))))

(defun analyze-lambda-scope (build lambda-list binding-domains &key package open local method returns specials call-inputs variable-tail key-inputs unknown-key-tail next original)
  (let* ((contract (lambda-contract build lambda-list :method method))
         (positional (lambda-positional-variables contract))
         (inputs (lambda-input-variables contract)))
   (multiple-value-bind (scope ordinary initializers)
       (snowgrave:analyze-source-lambda-bindings
        lambda-list (cons (append specials *argument-domains*) (append specials *function-bindings*))
        (lambda (name initializer scope)
          (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
            (unless open (audit-external-shared-value build name initializer specials))
            (multiple-value-bind (code receipt)
                (call-with-initialization-default-effects
                 build name contract
                 (lambda ()
                   (cond (call-inputs nil)
                         (returns (source-return-domains build (list initializer) (if (eq returns t) #'value-domain returns)))
                         (t (transform-form build initializer package :open open :local local :next next :original original)))))
              (values (cons (if receipt (return-summary-primary receipt) (value-domain build initializer))
                            (function-expression-target initializer)) code))))
        (lambda (name kind fact scope)
          (let* ((specialp (or (assoc name specials) (special-variable-p build name)))
                 (input-domain (case kind
                               ((:required :optional)
                                (let ((index (position name positional)))
                                  (if (and call-inputs (eq kind :optional) (>= index (length binding-domains)))
                                      (if variable-tail
                                          (merge-value-domains
                                           build (car fact)
                                           (if (external-result-domain-p variable-tail) :external-result :unknown))
                                          (car fact))
                                      (or (nth index binding-domains) :unknown))))
                               (:key
                                (if call-inputs
                                    (let* ((spec (nth (position name (lambda-key-variables contract)) (getf contract :keys)))
                                           (provided (assoc (keyword-name spec) key-inputs)))
                                      (cond (provided (cdr provided))
                                            (unknown-key-tail
                                             (merge-value-domains
                                              build (car fact)
                                              (if (external-result-domain-p unknown-key-tail) :external-result :unknown)))
                                            (t (car fact))))
                                    (or (nth (position name inputs) binding-domains) :unknown)))
                               (:rest
                                (if (if call-inputs
                                        (or (external-result-domain-p variable-tail)
                                            (some #'external-result-domain-p
                                                  (nthcdr (min (length positional) (length binding-domains))
                                                          binding-domains)))
                                        (external-result-domain-p (nth (position name inputs) binding-domains)))
                                    :external-result 'list))
                               (:supplied-p 'boolean) (:aux (car fact)) (t :unknown)))
                 (domain (if specialp :unknown input-domain))
                 (target (if (and (eq kind :aux) (not specialp)) (cdr fact) :unknown)))
            (when (and specialp (not open) (not *collect-function-flow*)
                       (getf (build-declaration build) :external-operations)
                       (not (native-data-domain-p build input-domain)))
              (fail build 'snowgrave:unclosed-call :external-shared-state-representation
                    (format nil "Special parameter ~S needs a native binding-domain proof or an external state ABI." name)
                    :reachability))
            (cons (acons name domain (car scope)) (acons name target (cdr scope)))))
        :specialized-required-p method :source-key (build-source-key build) :path (list (build-identity build)))
    ;; The cell's generic validator owns keyword rejection. A method accepts
    ;; the union of keywords admitted by all applicable methods, including
    ;; keywords that are only consumed by a different method in the chain.
    (values scope
      (if (and method (not open) (getf contract :keyp) (not (getf contract :allow)))
          (let ((aux (position '&aux ordinary)))
            (append (if aux (subseq ordinary 0 aux) ordinary) '(&allow-other-keys)
                    (when aux (subseq ordinary aux))))
          ordinary) initializers))))

(defun method-parts (form)
  (let ((tail (cddr form)) (qualifiers nil))
    ;; NIL is the valid zero-argument lambda list, never a method qualifier.
    (loop while (and tail (car tail) (atom (car tail))) do (push (pop tail) qualifiers))
    (values (nreverse qualifiers) (car tail) (cdr tail))))

(defun map-specialized-lambda-list (build lambda-list)
  (let ((required t))
   (mapcar (lambda (item)
            (when (member item lambda-list-keywords) (setf required nil))
            (if (and required (consp item) (symbolp (cadr item))
                     (member-name (cadr item) (build-classes build)))
                (list (car item) (mapped-name (cadr item) (build-open-package build)))
                item)) lambda-list)))

(defun map-slot-type-classes (build type package)
  (cond ((and (symbolp type) (member-name type (build-classes build)))
         (mapped-name type package))
        ((consp type) (mapcar (lambda (part) (map-slot-type-classes build part package)) type))
        (t type)))

(defparameter *host-method-combinations*
  '(standard + and append list max min nconc or progn))

(defun authored-combination-name (build name)
  (snowgrave:find-authored-definition (build-source build) :method-combination name))

(defun open-generic-option (build option package)
  (if (eq (car option) :method-combination)
      (let ((name (second option)))
        (cond ((authored-combination-name build name)
               (list* :method-combination (mapped-name name package) (cddr option)))
              ((member name *host-method-combinations*) option)
              (t (fail build 'snowgrave:unsupported-definition :method-combination-provenance
                       "A custom method combination needs its defining form in the ordered source unit."))))
      option))

(defun source-generic-combination (build generic)
  (let* ((definition (snowgrave:find-authored-definition (build-source build) :generic generic))
         (form (when definition (snowgrave:authored-definition-form definition)))
         (option (assoc :method-combination (cdddr form))))
    (if option (second option) 'standard)))

(defun authored-short-combination-p (build name)
  (let* ((definition (snowgrave:find-authored-definition (build-source build) :method-combination name))
         (form (when definition (snowgrave:authored-definition-form definition))))
    (and form (or (null (cddr form)) (keywordp (third form))))))

(defun open-method-qualifiers (build generic qualifiers)
  (let ((name (source-generic-combination build generic)))
    (if (authored-short-combination-p build name)
        (substitute (mapped-name name (build-open-package build)) name qualifiers :test #'eq)
        qualifiers)))

(defun source-method-qualifiers (build generic method)
  (let ((name (source-generic-combination build generic))
        (qualifiers (sb-mop:method-qualifiers method)))
    (if (authored-short-combination-p build name)
        (substitute name (mapped-name name (build-open-package build)) qualifiers :test #'eq)
        qualifiers)))

(defun open-method-combination-definition (build form package)
  ;; The host owns method-group patterns, order expressions, combination
  ;; arguments and their lexical bindings. Its generated factory is ordinary
  ;; source; only that lambda re-enters the shared OPEN source transformer.
  ;; Quoted declarations and the host's isolated registration stay cold.
  (let* ((shortp (authored-short-combination-p build (second form)))
         (options (cddr form))
         (definition
           `(cl:define-method-combination ,(mapped-name (second form) package)
              ,@(if (and shortp (not (loop for tail on options by #'cddr
                                          thereis (eq (car tail) :operator))))
                    (append options (list :operator (second form))) options))))
    (if shortp definition
        (multiple-value-bind (expansion expandedp) (macroexpand-1 definition)
          (let* ((registration (and (consp expansion) (eq (first expansion) 'progn)
                                    (= (length expansion) 3) (third expansion)))
                 (function (and (consp registration) (fourth registration))))
            (unless (and expandedp (consp registration)
                         (eq (first registration) 'sb-pcl::load-long-defcombin)
                         (consp function) (eq (first function) 'function)
                         (consp (second function)) (eq (caadr function) 'lambda))
              (fail build 'snowgrave:unsupported-definition :host-method-combination-expansion
                    "This host does not expose the expected ordinary method-combination factory lambda." :source-admission))
            (let* ((*cold-method-combination-factory* t)
                   (*cold-recipe-functions* (make-hash-table :test #'eq))
                   (*cold-recipe-source-marker* (gensym "COLD-RECIPE-SOURCE"))
                   (*cold-recipe-source-nodes* (cold-source-nodes form))
                   (factory (progn (audit-cold-method-group-predicates build form)
                                   (normalize-source-expression build (second function))))
                   (transformed (transform-form build factory package :open t))
                   (registration (copy-list registration)))
              (setf (fourth registration) `(function ,transformed))
              `(progn ,(second expansion) ,registration)))))))

(defun open-definition (build form)
  (setf (build-source-key build) (authored-source-key build form))
  (let ((package (build-open-package build)) (*immediate-lambda-domains* nil))
    (case (defining-kind form)
      (:class
       (unless (every (lambda (name) (member-name name (build-classes build))) (caddr form))
         (fail build 'snowgrave:unsupported-definition :external-superclass
               "Every authored superclass must join the sealed class cohort."))
       (unless (every (lambda (option) (member (car option) '(:documentation :default-initargs))) (cddddr form))
         (fail build 'snowgrave:unsupported-definition :class-options
               "Only standard documentation and default initargs have closed realization."))
       `(cl:defclass ,(mapped-name (cadr form) package)
            ,(mapcar (lambda (name)
                       (if (member-name name (build-classes build))
                           (mapped-name name package) name)) (caddr form))
          ,(mapcar (lambda (slot)
                     (unless (serializable-tree-p (if (symbolp slot) slot (car slot)))
                       (fail build 'snowgrave:nonreproducible-source :slot-identity
                             "A closed slot needs an interned stable name."))
                     (if (symbolp slot) slot
                         (cons (car slot)
                               (loop for (option value) on (cdr slot) by #'cddr
                                     append
                                     (cond ((member option '(:reader :writer :accessor))
                                            (list option (mapped-name value package)))
                                           ((member option '(:initarg :documentation))
                                            (list option value))
                                           ((eq option :type)
                                            (unless (snowgrave::explicit-slot-type-p value (build-classes build))
                                              (fail build 'snowgrave:unsupported-definition :typed-slot
                                                    "This slot type lacks a numeric/vector or sealed class-reference contract."))
                                            (list option (map-slot-type-classes build value package)))
                                           ((eq option :initform)
                                            (list option (transform-form build value package :open t)))
                                           ((eq option :allocation)
                                            (unless (eq value :instance)
                                              (fail build 'snowgrave:unsupported-definition :class-allocated-slot
                                                    "Class allocation needs a shared closed cell."))
                                            (list option value))
                                           (t (fail build 'snowgrave:unsupported-definition :slot-option
                                                    "Slot initialization extensions are not silently dropped.")))))))
                   (fourth form))
          ,@(mapcar (lambda (option)
                      (if (eq (car option) :default-initargs)
                          (cons :default-initargs
                                (loop for (key value) on (cdr option) by #'cddr
                                      append (list key (transform-form build value package :open t)))) option))
                    (cddddr form))))
      (:method-combination
       (open-method-combination-definition build form package))
      (:generic `(cl:defgeneric ,(mapped-name (cadr form) package) ,(third form)
                    ,@(mapcar (lambda (option) (open-generic-option build option package))
                              (cdddr form))))
      (:method
       (multiple-value-bind (qualifiers lambda-list body) (method-parts form)
        (let ((*argument-domains* nil) (*function-bindings* nil)
              (*local-function-frames* nil) (*value-domain-local-functions* nil)
              (*immediate-lambda-domains* nil))
         (multiple-value-bind (scope ordinary)
             (analyze-lambda-scope build lambda-list nil :package package :open t :method t :specials (body-special-domains body))
          (let ((required (length (ordinary-lambda-list build lambda-list :method t)))
                (*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
         (when (initialization-generic-p (cadr form))
           (unless (and (consp (car lambda-list))
                        (member-name (cadar lambda-list) (build-classes build))
                        (member-name (cadr form) (getf (build-declaration build) :closed-generics))
                        (= required (if (eq (cadr form) 'initialize-instance) 1 2))
                        (or (eq (cadr form) 'initialize-instance)
                            (and (= required 2)
                                 (or (symbolp (cadr lambda-list))
                                     (equal (cdadr lambda-list) '(t))))))
             (fail build 'snowgrave:unclosed-class-operation :initialization-method-domain
                   "Initialization methods must be selected and specialize a disposable class, with a universal slot-names axis.")))
         `(cl:defmethod ,(if (initialization-generic-p (cadr form)) (cadr form)
                             (mapped-name (cadr form) package))
              ,@(open-method-qualifiers build (cadr form) qualifiers)
              ,(append (map-specialized-lambda-list build (subseq lambda-list 0 required))
                       (nthcdr required ordinary))
            (declare (special ,@(source-specials build)))
            ,@(preserve-source-block (cadr form) (transform-body build body package :open t))))))))
      (:function
       (let ((*argument-domains* nil) (*function-bindings* nil)
              (*local-function-frames* nil) (*value-domain-local-functions* nil)
              (*immediate-lambda-domains* nil))
        (multiple-value-bind (scope ordinary)
            (analyze-lambda-scope build (caddr form) nil :package package :open t
                                 :specials (body-special-domains (cdddr form)))
         (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
         `(defun ,(mapped-name (cadr form) package)
            ,ordinary
            ,@(preserve-source-block (cadr form) (transform-body build (cdddr form) package :open t)))))))
      (:global
       (unless (or (= (length form) 2) (reproducible-global-p build (caddr form) t))
         (fail build 'snowgrave:nonreproducible-source :global-initializer
               "Global initializers admit constants, checked captures, pure construction, and literal-named fresh symbol recipes."))
       `(,(car form) ,(global-binding-name build (cadr form) package t)
         ,@(when (> (length form) 2)
             (cons (transform-global-initializer build (caddr form) package :open t) (cdddr form))))))))

(defun fresh-symbol-initializer-p (build form)
  ;; This is an allocation recipe, separate from pure constant construction.
  ;; Names are frozen source strings; dynamic/side-effecting name expressions
  ;; and caller-supplied uninterned symbols have no admitted capture mapping.
  (and (consp form) (eq (first form) 'make-symbol)
       (snowgrave::source-finite-list-p form) (= (length form) 2)
       (standard-operation-meaning-p build 'make-symbol)
       (or (stringp (second form))
           (multiple-value-bind (name constantp) (quoted-value (second form))
             (and constantp (stringp name))))))

(defun transform-global-initializer (build form package &key open)
  (let ((*cold-global-initializer* t))
    (transform-form build form package :open open)))

(defun reproducible-global-p (build form &optional fresh-symbols-p)
  (cond ((reproducible-integer-p build form) t)
        ((atom form) (or (numberp form) (stringp form) (characterp form)
                        (keywordp form) (eq form t) (null form)))
        ((eq (car form) 'quote) (serializable-literal-graph-p (cadr form) (build-literal-states build)))
        ((and fresh-symbols-p (fresh-symbol-initializer-p build form)) t)
        ((eq (car form) 'function) (function-target-p build (cadr form) nil))
        ((eq (car form) 'load-time-value) (reproducible-global-p build (cadr form)))
        ((member (car form) *reproducible-global-operations*)
         (every (lambda (x) (reproducible-global-p build x fresh-symbols-p)) (cdr form)))
        (t nil)))

(defun reproducible-integer-operation-p (build name &optional local)
  "A stable primitive identity for callers that prove integer arguments."
  (let ((native (assoc name *native-ordinary-functions*)))
    (and (member name *reproducible-integer-operations*)
         (standard-operation-meaning-p build name local)
         native (fboundp name) (eq (fdefinition name) (cdr native)))))

(defun reproducible-integer-p (build form)
  ;; This is a structural result/effect proof, not a constant evaluator.
  ;; The original expression executes in both compilations and installations.
  (cond
    ((integerp form) t)
    ((symbolp form)
     (let ((constant (assoc form *standard-integer-constants*)))
       (when (and constant (not (member form (build-globals build)))
                  (eq (sb-int:info :variable :kind form) :constant)
                  (boundp form) (eql (symbol-value form) (cdr constant)))
         (pushnew (list :name-key (snowgrave::function-name-key form)
                        :host-value (cdr constant))
                  (build-integer-constants build) :test #'equal)
         t)))
    ((and (consp form) (eq (first form) 'quote))
     (and (= (length form) 2) (integerp (second form))))
    ((and (consp form) (reproducible-integer-operation-p build (first form)))
     (every (lambda (argument) (reproducible-integer-p build argument)) (rest form)))
    (t nil)))

(defun cold-integer-constant-evidence (build)
  (sort (copy-tree (build-integer-constants build)) #'string<
        :key (lambda (constant) (prin1-to-string (getf constant :name-key)))))

(defun staged-special-form (form specials)
  (if (member (cadr form) specials)
   (case (car form)
    (defparameter `(setf (symbol-value ',(cadr form)) ,(caddr form)))
    (defvar (if (> (length form) 2)
                `(unless (boundp ',(cadr form)) (setf (symbol-value ',(cadr form)) ,(caddr form)))
                '(values)))
    (t form)) form))

(defun literal-reference (build value package)
  (when (eq package (build-output-package build))
    (setf value (graph-literal-origin build value)))
  (when (and (eq package (build-output-package build)) (graph-source-node build value))
    (return-from literal-reference (graph-literal-reference build value)))
  ;; EQ is the source graph's authority, not structural equality. Separate
  ;; pools keep the disposable CLOS pass and the installed unit independent.
  (unless (serializable-literal-graph-p value (build-literal-states build))
    (fail build 'snowgrave:residual-metaobject :literal-object
          "Literal graphs must contain only readable native data."))
  (let* ((pool (or (cdr (assoc package (build-literal-pools build)))
                   (let ((pool (make-literal-pool)))
                     ;; Use an interned, private binding for fresh-file replay.
                     (setf (literal-pool-name pool) (intern (symbol-name (gensym "LITERALS")) package))
                     (push (cons package pool) (build-literal-pools build))
                     pool)))
         (index (or (gethash value (literal-pool-indices pool))
                    (setf (gethash value (literal-pool-indices pool))
                          (vector-push-extend value (literal-pool-values pool))))))
    ;; Retain the literal's native type for ordinary array/string lowering;
    ;; an opaque LOAD-TIME-VALUE would otherwise lose that compiler fact.
    ;; Even an ordinary outer literal can share a captured mutable child after
    ;; provenance is joined by the pool. Keep that whole installation mutable.
    `(the ,(type-of value)
       (load-time-value (svref ,(literal-pool-name pool) ,index)
         ,(not (and (eq package (build-output-package build)) (build-graph-root-names build)))))))

(defun literal-pool-definition (build package)
  (let ((pool (cdr (assoc package (build-literal-pools build)))))
    (when pool
      (let ((seen (make-hash-table :test #'eq)) (defaults (make-hash-table :test #'eq))
            (bindings nil) (edges nil) (pending nil))
        (labels ((reference (value)
                   (when (eq package (build-output-package build))
                     (setf value (graph-literal-origin build value)))
                   (let ((row (and (eq package (build-output-package build))
                                   (graph-source-node build value))))
                    (cond ((and row (getf row :import-reference)) (getf row :import-reference))
                          ((or (consp value) (arrayp value) (and row (getf row :class)))
                           (or (gethash value seen)
                               (let* ((parent (when (arrayp value)
                                                (if row (getf row :backing) (array-displacement value))))
                                      (backing (when parent (reference parent)))
                                      (name (gensym "LITERAL"))
                                      (payload (when (arrayp value)
                                                 (if row (getf row :values)
                                                     (unless (or parent (null (array-element-type value)))
                                                       (loop for i below (array-total-size value)
                                                             collect (row-major-aref value i))))))
                                      (default (when payload
                                                 (let ((first (car payload)))
                                                   (list (if (or (numberp first) (characterp first) (symbolp first)) first nil)))))
                                      (initializer
                                        (cond ((and row (getf row :class))
                                               `(snowgrave:sg-make-record ,(ensure-layout build (getf row :class))))
                                              ((consp value) '(cons nil nil))
                                              (t `(make-array ',(if row (getf row :dimensions) (array-dimensions value))
                                                    ,@(loop for (key argument) on
                                                            (if row (getf row :options)
                                                                (snowgrave::array-allocation-options value backing)) by #'cddr
                                                            append (list key (if (eq key :displaced-to) backing `',argument)))
                                                    ,@(when default `(:initial-element ',(car default))))))))
                                 (setf (gethash value seen) name)
                                 (when default (setf (gethash value defaults) default))
                                 (push (list name initializer) bindings)
                                 (unless (and (arrayp value) (or parent (null (array-element-type value))))
                                   (push (list name value row payload) pending))
                                 name)))
                          (t `',value)))))
          (let ((roots (map 'list #'reference (literal-pool-values pool))))
            (loop while pending for (name value row payload) = (pop pending) do
              (cond ((and row (getf row :class))
                     (dolist (field (getf row :values))
                       (when (second field)
                         (push `(snowgrave:sg-record-write ,name ',(first field) ,(reference (third field))) edges))))
                    ((consp value)
                     (let ((parts (if row (getf row :values) (list (car value) (cdr value)))))
                       (push `(setf (car ,name) ,(reference (first parts))
                                    (cdr ,name) ,(reference (second parts))) edges)))
                    (t (loop for element in payload for index from 0 do
                         (let ((default (gethash value defaults)))
                           (unless (and default (eql element (car default)))
                             (push `(setf (row-major-aref ,name ,index) ,(reference element)) edges)))))))
            ;; One identity inventory and shell/fill recipe handles both native
            ;; literals and admitted configuration records. Imported nodes are
            ;; references and never receive initializer/fill effects.
            `(defparameter ,(literal-pool-name pool)
               (let* ,(nreverse bindings) ,@(nreverse edges) (vector ,@roots)))))))))

(defun with-literal-pool (build forms package)
  (let* ((definition (literal-pool-definition build package))
         (configurationp (and (eq package (build-output-package build))
                              (build-graph-root-names build)))
         (ordered
           (cond ((null definition) forms)
                 (configurationp
                  ;; Native validation precedes layouts; both precede record
                  ;; shells. Keep the ordinary/open native literal prefix.
                  (let ((prefix nil) (rest forms))
                    (loop while (and rest
                                     (let ((form (car rest)))
                                       (and (eq (car form) 'defparameter)
                                            (or (eq (second form) (build-reference-domain-name build))
                                                (member (second form) (build-layout-names build) :key #'cdr)
                                                (eq (second form) (build-graph-resource-name build))
                                                (find (second form) (build-graph-imports build)
                                                      :key (lambda (binding) (getf (cdr binding) :name)))))))
                          do (push (pop rest) prefix))
                    (append (nreverse prefix) (list definition) rest)))
                 (t (cons definition forms)))))
    (if configurationp
        ;; Reserve the incarnation before any resource/layout/root cell can be
        ;; changed, including a second load after an incomplete installation.
        (let ((seal (fresh-name build "CONFIGURATION-INCARNATION")))
          (cons `(defparameter ,seal
                   (if (boundp ',seal)
                       (snowgrave::native-binding-error ',(build-identity build)
                         :configuration-incarnation "A configuration identity has already been installed.")
                       t))
                ordered))
        ordered)))

(defun compile-forms (build forms phase &key stage-specials)
  (flet ((run ()
           (let ((*package* (find-package :cl)))
             (uiop:with-temporary-file (:pathname source :stream stream :type "lisp")
               (let ((*print-readably* t) (*print-circle* t))
                 ;; One read scope retains shared literal payload across
                 ;; definitions; top-level PROGN retains compile-file semantics.
                 (write `(progn ,@(if stage-specials
                                     (mapcar (lambda (form) (staged-special-form form stage-specials)) forms)
                                     forms)) :stream stream)
                 (terpri stream))
               (finish-output stream)
               (multiple-value-bind (fasl warnings failure) (compile-file source)
                 (declare (ignore warnings))
                 (when failure
                   (fail build 'snowgrave:unsupported-definition :compiler-failure
                         "The host compiler rejected the emitted source." phase))
                 (unwind-protect (load fasl) (when (probe-file fasl) (delete-file fasl))))))))
    (if stage-specials
        (progv stage-specials nil
          (run)
          (mapcar (lambda (name) (list name (boundp name) (when (boundp name) (symbol-value name)))) stage-specials))
        (progn (run) nil))))

(defun class-closure (root)
  (let ((result nil))
    (labels ((visit (class)
               (unless (member class result :test #'eq)
                 (push class result)
                 (dolist (subclass (sb-mop:class-direct-subclasses class)) (visit subclass)))))
      (visit root))
    (sort result (lambda (a b)
                   (let ((ac (length (sb-mop:class-precedence-list a)))
                         (bc (length (sb-mop:class-precedence-list b))))
                     (if (= ac bc)
                         (string< (symbol-name (sb-mop:class-name a))
                                  (symbol-name (sb-mop:class-name b)))
                         (> ac bc)))))))

(defun source-class (build class)
  (or (find (sb-mop:class-name class) (build-classes build)
            :key (lambda (name) (mapped-name name (build-open-package build))) :test #'eq)
      (sb-mop:class-name class)))

(defun authored-class-form (build class)
  (let ((definition (snowgrave:find-authored-definition (build-source build) :class (source-class build class))))
    (and definition (normalized-definition-form build definition))))

(defun unique-authored-initializer (build candidates feature)
  ;; The MOP chooses the initializer function. Recover only that actual
  ;; function's authored expression, retaining its owned literal graph.
  ;; Equality of freshly read initforms cannot prove literal alias identity.
  (unless (and candidates
               (every (lambda (candidate)
                        (eq (getf candidate :form) (getf (car candidates) :form))) candidates))
    (fail build 'snowgrave:nonreproducible-source feature
          "The actual finalized initializer lacks unambiguous authored constant provenance." :materialization))
  ;; Candidates were pushed in CPL order. If the actual host initfunction is
  ;; shared by identical owned expressions, retain the most specific source
  ;; owner without changing the initializer/literal chosen by the MOP.
  (car (last candidates)))

(defun class-initializer-provenance (build class)
  "Index actual direct initializer functions once per finalized layout.
Effective-slot/default selection remains the MOP's; this is source provenance,
not a second inheritance or initialization algorithm."
  (let ((slots (make-hash-table :test #'equal)) (defaults (make-hash-table :test #'equal)))
    (dolist (ancestor (sb-mop:class-precedence-list class))
      (let ((form (authored-class-form build ancestor)))
        (when form
          (let ((source-slots (make-hash-table :test #'eq)))
            (dolist (source (fourth form))
              (setf (gethash (if (consp source) (car source) source) source-slots) source))
            (dolist (direct (sb-mop:class-direct-slots ancestor))
              (when (sb-mop:slot-definition-initfunction direct)
                (let ((source (gethash (sb-mop:slot-definition-name direct) source-slots)))
                  (when (and (consp source) (member :initform (cdr source)))
                    (push (list :form (getf (cdr source) :initform)
                                :source-key (authored-source-key build form))
                          (gethash (list (sb-mop:slot-definition-name direct)
                                         (sb-mop:slot-definition-initfunction direct)) slots)))))))
          (let ((source-defaults (make-hash-table :test #'eq)))
            (loop for (key value) on (cdr (assoc :default-initargs (cddddr form))) by #'cddr
                  do (setf (gethash key source-defaults)
                           (list :form value :source-key (authored-source-key build form))))
          (dolist (direct (sb-mop:class-direct-default-initargs ancestor))
              (let ((source (gethash (car direct) source-defaults)))
                (when source
                  (push source (gethash (list (car direct) (third direct)) defaults)))))))))
    (values slots defaults)))

(defun obtain-layouts (build)
  (dolist (name (reverse (build-classes build)))
    (let ((class (find-class (mapped-name name (build-open-package build)))))
      (unless (eq (class-of class) (find-class 'standard-class))
        (fail build 'snowgrave:unsupported-definition :metaclass
              "A custom metaclass needs an exact representation extension." :materialization))
      (sb-mop:finalize-inheritance class)
      (multiple-value-bind (slot-provenance default-provenance) (class-initializer-provenance build class)
       (let ((slots (sb-mop:class-slots class)))
        (unless (every (lambda (slot) (eq (sb-mop:slot-definition-allocation slot) :instance)) slots)
          (fail build 'snowgrave:unsupported-definition :class-slot
                "Class slots require shared closed storage." :materialization))
        (push (list :class name :identity (list (build-identity build) name :version 1)
                    :construction-protocol nil :construction-reached-p nil :construction-state nil
                    :class-token (snowgrave::class-identity-token (list (build-identity build) name :version 1) name)
                    :error-mapping (slot-error-mapping build class)
                    :slots (mapcar #'sb-mop:slot-definition-name slots)
                    :slot-types (mapcar (lambda (slot)
                                          (let ((type (restore-source-names build (sb-mop:slot-definition-type slot))))
                                            (unless (snowgrave::explicit-slot-type-p type (build-classes build))
                                              (fail build 'snowgrave:unsupported-definition :typed-slot
                                                    "The effective slot type has no closed realization." :materialization))
                                            type)) slots)
                    :slot-initargs (mapcar #'sb-mop:slot-definition-initargs slots)
                    :slot-initforms (mapcar (lambda (slot)
                                             (when (sb-mop:slot-definition-initfunction slot)
                                               (unique-authored-initializer build
                                                 (gethash (list (sb-mop:slot-definition-name slot)
                                                                (sb-mop:slot-definition-initfunction slot)) slot-provenance)
                                                 :slot-initform-provenance))) slots)
                    :default-initargs (mapcar (lambda (default)
                                               (let ((initializer (unique-authored-initializer build
                                                        (gethash (list (car default) (third default)) default-provenance)
                                                        :default-initform-provenance)))
                                                 (list (car default) (getf initializer :form)
                                                       :source-key (getf initializer :source-key))))
                                             (sb-mop:class-default-initargs class))
                    :ancestors (remove-if-not
                                (lambda (ancestor) (member-name ancestor (build-classes build)))
                                (mapcar (lambda (ancestor) (source-class build ancestor))
                                        (sb-mop:class-precedence-list class))))
              (build-layouts build))))))
  (setf (build-layouts build) (nreverse (build-layouts build))))

(defun slot-error-mapping (build class)
  ;; Verify the default protocol over the whole receiver domain, not one
  ;; successful sample. EQL-specialized or authored host methods require an
  ;; effective-method mapping before this ordinary hosted descriptor is sound.
  (dolist (baseline *standard-slot-methods*)
    (dolist (slot-class '(symbol null))
      (multiple-value-bind (methods certainp)
          (sb-mop:compute-applicable-methods-using-classes
           (fdefinition (first baseline))
           (append (list (class-of class) class (find-class slot-class))
                   (when (eq (first baseline) 'slot-missing) (list (find-class 'symbol)))))
        (unless (and certainp (= (length methods) 1)
                     (eq (first methods) (second baseline))
                     (eq (sb-mop:method-function (first methods)) (third baseline))
                     (let* ((source (sb-introspect:find-definition-source (third baseline)))
                            (pathname (and source (sb-introspect:definition-source-pathname source))))
                       (and (typep pathname 'logical-pathname)
                            (string= (host-namestring pathname) "SYS"))))
          (fail build 'snowgrave:unclosed-class-operation :extended-slot-protocol
                "Additional or replaced SLOT-MISSING/SLOT-UNBOUND methods need exact effective protocol materialization." :materialization)))))
  (dolist (function *standard-slot-functions*)
    (unless (and (eq (fdefinition (car function)) (cdr function))
                 (let* ((source (sb-introspect:find-definition-source (cdr function)))
                        (pathname (and source (sb-introspect:definition-source-pathname source))))
                   (and (typep pathname 'logical-pathname)
                        (string= (host-namestring pathname) "SYS"))))
      (fail build 'snowgrave:unclosed-class-operation :replaced-slot-error-helper
            "A replaced restart reader or slot-name printer needs an exact error mapping." :materialization)))
  (let ((condition (handler-case
                       (slot-missing class (sb-mop:class-prototype class)
                                     (make-symbol "SNOWGRAVE-MISSING-PROBE") 'slot-value)
                     (sb-pcl::missing-slot (condition) condition))))
    (unless (typep condition 'sb-pcl::missing-slot)
      (fail build 'snowgrave:unclosed-class-operation :missing-slot-condition
            "The native missing-slot condition does not match the hosted error contract." :materialization))
    (list :host :sbcl :host-type (lisp-implementation-type) :host-version (lisp-implementation-version)
        :missing-condition (type-of condition)
        :missing-control (simple-condition-format-control condition)
        :writer-control "set the slot's value to ~S (SETF of SLOT-VALUE)"
        :hint-control "It has a slot ~/sb-ext:print-symbol-with-prefix/, while ~/sb-ext:print-symbol-with-prefix/ is requested."
        :operations '((slot-value . "read the slot's value (slot-value)")
                      (slot-boundp . "test to see whether slot is bound (SLOT-BOUNDP)")
                      (slot-makunbound . "make the slot unbound (SLOT-MAKUNBOUND)"))
        :interactive 'sb-int:read-evaluated-form
        :ordinary-intrinsics '(sb-int:read-evaluated-form sb-ext:print-symbol-with-prefix))))

(defun restore-source-names (build value)
  (cond ((and (symbolp value) (eq (symbol-package value) (build-open-package build)))
         (or (let ((source (find value
                   (append (build-classes build) (build-functions build) (build-globals build)
                           (getf (build-declaration build) :closed-generics))
                   :key (lambda (name) (mapped-name (if (consp name) (cadr name) name) (build-open-package build)))
                   :test #'eq)))
               (if (consp source) (cadr source) source))
             (fail build 'snowgrave:nonreproducible-source :initform-provenance
                   "An initialization form contains an untracked builder symbol." :materialization)))
        ((consp value) (cons (restore-source-names build (car value)) (restore-source-names build (cdr value))))
        (t value)))

(defun standard-initialization-method-p (build operation method)
  (let* ((baseline (assoc operation *standard-initialization-methods*))
         (source (sb-introspect:find-definition-source (sb-mop:method-function method)))
         (pathname (and source (sb-introspect:definition-source-pathname source))))
    (unless (and (eq method (second baseline))
                 (eq (sb-mop:method-function method) (third baseline))
                 (typep pathname 'logical-pathname)
                 (string= (host-namestring pathname) "SYS"))
      (fail build 'snowgrave:unclosed-class-operation :extended-initialization
            "A replaced host initialization primary requires an exact materialization mapping." :materialization))
    t))

(defun initialization-methods (build operation class)
  (multiple-value-bind (methods certainp)
      (sb-mop:compute-applicable-methods-using-classes
       (fdefinition operation)
       (if (eq operation 'allocate-instance) (list (class-of class))
           (append (list class) (when (eq operation 'shared-initialize) (list (find-class t))))))
    (unless certainp
      (fail build 'snowgrave:mop-failure :initialization-applicability
            "Initialization applicability requires exact class-only evidence." :materialization))
    (dolist (method methods)
      (unless (and (not (eq operation 'allocate-instance))
                   (authored-method build operation method))
        (standard-initialization-method-p build operation method)))
    methods))

(defun construction-initarg-contract (build class)
  (let* ((description (find (source-class build class) (build-layouts build)
                            :key (lambda (layout) (getf layout :class)) :test #'name=))
         (legal (copy-list (apply #'append (getf description :slot-initargs))))
         (allow nil))
    (dolist (operation '(allocate-instance initialize-instance shared-initialize))
      (dolist (method (initialization-methods build operation class))
        (let ((contract (lambda-contract build (sb-mop:method-lambda-list method))))
          (dolist (key (getf contract :keys)) (pushnew (keyword-name key) legal))
          (when (getf contract :allow) (setf allow t)))))
    (values legal allow)))

(defun verify-standard-construction (build class)
  (dolist (function *standard-initarg-functions*)
    (unless (eq (fdefinition (car function)) (cdr function))
      (fail build 'snowgrave:unclosed-class-operation :replaced-initarg-validator
            "A replaced host initialization argument validator requires an exact error mapping." :materialization)))
  (dolist (contract (list (cons 'symbol (find-class 'symbol)) (cons 'class (class-of class))))
    (multiple-value-bind (methods certainp)
        (sb-mop:compute-applicable-methods-using-classes #'make-instance (list (cdr contract)))
      (let* ((baseline (assoc (car contract) *standard-construction-methods*))
             (method (first methods)))
        (unless (and certainp (= (length methods) 1)
                     (eq method (second baseline))
                     (eq (sb-mop:method-function method) (third baseline)))
          (fail build 'snowgrave:unclosed-class-operation :extended-make-instance
                "Additional or replaced MAKE-INSTANCE methods require effective protocol materialization." :materialization)))))
  t)

(defun emit-standard-shared-call (build parameters)
  (let* ((class (first *cell-domains*))
         (description (find class (build-layouts build) :key (lambda (layout) (getf layout :class)) :test #'name=))
         (name (fresh-name build "SHARED-PRIMARY"))
         (record (fresh-name build "RECORD"))
         (slots (fresh-name build "SLOT-NAMES"))
         (arguments (fresh-name build "INITARGS"))
         (key-var (fresh-name build "KEY"))
         (value-var (fresh-name build "VALUE"))
         (tail-var (fresh-name build "TAIL")))
    (push name (build-method-names build))
    (push `(defun ,name ,parameters
             (destructuring-bind (,record ,slots &rest ,arguments) ,(car parameters)
               ,@(mapcar
                  (lambda (slot initargs initform)
                    `(multiple-value-bind (,key-var ,value-var ,tail-var)
                         (get-properties ,arguments ',initargs)
                       (declare (ignore ,key-var))
                       (cond (,tail-var (snowgrave::%record-write ,record ',slot ,value-var '(,class)))
                             ,@(when initform
                                 `(((and (or (eq ,slots t) (member ',slot ,slots))
                                          (not (snowgrave::%record-boundp ,record ',slot '(,class))))
                                    (snowgrave::%record-write
                                     ,record ',slot
                                     ,(with-build-source-key (build (getf initform :source-key))
                                        (call-in-initializer-environment build initform
                                          (lambda ()
                                            (audit-construction-slot-domain build description slot
                                              (value-domain build (getf initform :form)))
                                            (transform-form build (getf initform :form) (build-output-package build))))) '(,class))))))))
                  (getf description :slots) (getf description :slot-initargs) (getf description :slot-initforms))
               ,record))
          (build-generated build))
    `(,name ,@parameters)))

(defun emit-initialization-generic (build generic)
  (when (eq generic 'initialize-instance)
    (retain-construction-initialization build))
  (let* ((*fixed-effective-arguments* nil)
         (gf (fdefinition generic))
         (record (fresh-name build "RECORD"))
         (slots (when (eq generic 'shared-initialize) (fresh-name build "SLOT-NAMES")))
         (tail (fresh-name build "INITARGS"))
         (arguments (fresh-name build "ARGUMENTS"))
         (clauses nil) (descriptions nil))
    (validate-generic-protocol build generic gf)
    (dolist (layout (build-layouts build))
      (let* ((class (getf layout :class))
             (host-class (find-class (mapped-name class (build-open-package build))))
             (methods (initialization-methods build generic host-class))
             (*cell-domains* (append (list class) (when slots (list t))))
             (*initialization-phase* (when (graph-state-profile-p build)
                                      (make-initialization-root-phase build generic class)))
             (*initialization-next* nil))
        (multiple-value-bind (effective options)
            (sb-mop:compute-effective-method gf (sb-mop:generic-function-method-combination gf) methods)
          (when options (fail build 'snowgrave:unsupported-definition :effective-method-options
                              "Initialization MOP options require normalization." :materialization))
          (let ((validator (emit-argument-validator build generic gf methods)))
            (push `(,(record-layout-test build class record)
                     (apply #',validator ,arguments)
                     ,(if *initialization-phase*
                          (emit-initialization-plan build generic effective (list arguments))
                          (emit-effective build generic effective (list arguments)))) clauses)))
        (push (list :classes (append (list class) (when slots (list t)))
                    :methods (mapcar (lambda (method) (method-logical-key build generic method)) methods)) descriptions)))
    (push `(defun ,(mapped-name generic (build-output-package build)) (,record ,@(when slots (list slots)) &rest ,tail)
             (let ((,arguments (list* ,record ,@(when slots (list slots)) ,tail)))
               (cond ,@(nreverse clauses)
                     (t (snowgrave:sg-domain-violation ',(build-identity build) ',generic ,arguments)))))
          (build-generated build))
    (list :generic generic :lambda-list (sb-mop:generic-function-lambda-list gf)
          :protocol :materialized-initialization :cells (nreverse descriptions))))

(defun ensure-reference-domain (build)
  (or (build-reference-domain-name build)
      (when (some (lambda (layout)
                    (some (lambda (type)
                            (snowgrave::class-reference-slot-type-p type (build-classes build)))
                          (getf layout :slot-types))) (build-layouts build))
        (let ((name (fresh-name build "REFERENCE-DOMAIN")))
          (push `(defparameter ,name
                   (snowgrave:make-reference-domain ',(build-identity build)
                                                    ',(mapcar #'layout-metadata (build-layouts build))))
                (build-generated build))
          (setf (build-reference-domain-name build) name)))))

(defun ensure-layout (build class)
  (or (cdr (assoc class (build-layout-names build) :test #'name=))
      (let* ((description (find class (build-layouts build)
                                :key (lambda (layout) (getf layout :class)) :test #'name=))
             (reference-domain (ensure-reference-domain build))
             (name (fresh-name build "LAYOUT")))
        (unless description (fail build 'snowgrave:unclosed-class-operation :layout-domain
                                  "An exact layout needs an admitted class row." :materialization))
        (push `(defparameter ,name
                 (snowgrave:make-layout ',(getf description :identity) ',class
                                        ',(getf description :ancestors) ',(getf description :slots)
                                        :slot-types ',(getf description :slot-types)
                                        ,@(when reference-domain `(:reference-domain ,reference-domain))
                                        :error-mapping ',(getf description :error-mapping)))
              (build-generated build))
        (push (cons class name) (build-layout-names build))
        name)))

(defun ensure-admitted-layouts (build)
  ;; Called before inference snapshots persistent generated state. Provision
  ;; descriptors even when the unit never invokes any class's constructor.
  (ensure-reference-domain build)
  (dolist (description (build-layouts build))
    (ensure-layout build (getf description :class))))

(defun ensure-constructor (build class)
  (or (cdr (assoc class (build-constructors build) :test #'name=))
      (let* ((description (find class (build-layouts build) :key (lambda (layout) (getf layout :class)) :test #'name=))
             (name (fresh-name build "CONSTRUCTOR"))
             (layout (ensure-layout build class))
             (arguments (fresh-name build "INITARGS"))
             (defaults (fresh-name build "DEFAULTS"))
             (record (fresh-name build "RECORD"))
             (key-var (fresh-name build "KEY"))
             (value-var (fresh-name build "VALUE"))
             (tail-var (fresh-name build "TAIL"))
             (invalid (fresh-name build "INVALID-KEYS"))
             (legal nil) (allow nil)
             (*argument-domains* nil) (*function-bindings* nil)
             (*local-function-frames* nil) (*value-domain-local-functions* nil)
             (*mutable-invariant-bindings* nil) (*declared-specials* nil)
             (*current-method* nil) (*tagbody-targets* nil) (*immediate-lambda-domains* nil)
             (*initialization-phase* nil) (*initialization-next* nil) (*initialization-plan* nil))
        (let ((host-class (find-class (mapped-name class (build-open-package build)))))
          (verify-standard-construction build host-class)
          (multiple-value-setq (legal allow) (construction-initarg-contract build host-class)))
        (setf (getf description :construction-initargs)
              (list :keywords legal :allow-other-keys allow :invalid-condition 'sb-pcl::initarg-error))
        (let ((selected (getf (build-declaration build) :closed-generics)))
          (unless (or (and (member-name 'initialize-instance selected) (member-name 'shared-initialize selected))
                      (and (not (some (lambda (form) (initialization-generic-p (cadr form))) (build-method-sources build)))
                           (not (member-name 'initialize-instance selected)) (not (member-name 'shared-initialize selected))))
            (fail build 'snowgrave:unclosed-class-operation :initialization-cohort
                  "Authored construction requires both initialization protocol generics in the closed cohort." :materialization)))
        (retain-construction-initialization build)
        (push (cons class name) (build-constructors build))
        (push `(defun ,name (&rest ,arguments)
                 (let ((,defaults nil))
                   ,@(mapcar
                      (lambda (default)
                        `(unless (nth-value 2 (get-properties ,arguments '(,(car default))))
                           (setf ,defaults (append ,defaults
                                                  (list ,(car default)
                                                        ,(with-build-source-key (build (getf (cddr default) :source-key))
                                                           (call-in-initializer-environment
                                                             build (list :source-key (getf (cddr default) :source-key))
                                                             (lambda ()
                                                               (audit-construction-initarg-domain build description (car default)
                                                                 (value-domain build (cadr default)))
                                                               (transform-form build (cadr default) (build-output-package build))))))))))
                      (getf description :default-initargs))
                   (let ((,arguments (append ,arguments ,defaults)))
                     ,@(unless allow
                         `((let ((,invalid nil))
                             (unless (getf ,arguments :allow-other-keys)
                               (loop for ,tail-var on ,arguments by #'cddr
                                     for ,key-var = (car ,tail-var)
                                     unless (or (eq ,key-var :allow-other-keys) (member ,key-var ',legal))
                                       do (push ,key-var ,invalid)))
                             (when ,invalid
                               (error 'sb-pcl::initarg-error :class ',(getf description :class-token)
                                      :initargs ,invalid)))))
                     (let ((,record (snowgrave:sg-make-record ,layout)))
                     ,@(if (member-name 'initialize-instance (getf (build-declaration build) :closed-generics))
                           `((apply #',(mapped-name 'initialize-instance (build-output-package build)) ,record ,arguments))
                           (mapcar
                        (lambda (slot initargs initform)
                          `(multiple-value-bind (,key-var ,value-var ,tail-var)
                               (get-properties ,arguments ',initargs)
                             (declare (ignore ,key-var))
                             (cond (,tail-var (snowgrave::%record-write ,record ',slot ,value-var '(,class)))
                                   ,@(when initform
                                       `((t (snowgrave::%record-write
                                             ,record ',slot
                                             ,(with-build-source-key (build (getf initform :source-key))
                                                (call-in-initializer-environment build initform
                                                  (lambda ()
                                                    (audit-construction-slot-domain build description slot
                                                      (value-domain build (getf initform :form)))
                                                    (transform-form build (getf initform :form) (build-output-package build))))) '(,class))))))))
                        (getf description :slots) (getf description :slot-initargs) (getf description :slot-initforms)))
                     ,record))))
              (build-generated build))
        name)))

(defun authored-method (build generic method)
  (or
   (find-if
    (lambda (form)
      (and (name= (cadr form) generic)
           (multiple-value-bind (qualifiers lambda-list body) (method-parts form)
             (declare (ignore body))
             (and (equal qualifiers (source-method-qualifiers build generic method))
                  (equal
                   (mapcar (lambda (item)
                             (let ((specializer (if (consp item) (cadr item) 't)))
                               (if (and (consp specializer) (eq (car specializer) 'eql))
                                   specializer
                                   (if (member-name specializer (build-classes build))
                                       (mapped-name specializer (build-open-package build)) specializer))))
                           (subseq lambda-list 0 (length (ordinary-lambda-list build lambda-list :method t))))
                   (mapcar (lambda (specializer)
                             (if (typep specializer 'sb-mop:eql-specializer)
                                 (list 'eql (list 'quote (sb-mop:eql-specializer-object specializer)))
                                 (sb-mop:class-name specializer)))
                           (sb-mop:method-specializers method)))))))
    (build-method-sources build))
   (when (and (eq generic 'initialize-instance)
              (eq method (second (assoc generic *standard-initialization-methods*))))
     (standard-initialization-method-p build generic method)
     '(snowgrave:defmethod initialize-instance (record &rest initargs)
        (apply #'shared-initialize record t initargs)))
   (when (typep method 'sb-mop:standard-accessor-method)
     (let* ((slot (sb-mop:slot-definition-name (sb-mop:accessor-method-slot-definition method)))
            (readerp (typep method 'sb-mop:standard-reader-method)))
       (if readerp
           `(snowgrave:defmethod ,generic ((record t))
              (snowgrave::%record-read record ',slot ',(list (first *cell-domains*))))
           `(snowgrave:defmethod ,generic (value (record t))
              (snowgrave::%record-write record ',slot value ',(list (second *cell-domains*)))))))))

(defun method-logical-key (build generic method)
  (list (build-identity build) :method generic
        (source-method-qualifiers build generic method)
        (mapcar (lambda (specializer) (source-class build specializer)) (sb-mop:method-specializers method))))

(defun method-source-key (build generic method form)
  (let ((definition (snowgrave::authored-form-definition
                     (build-source build)
                     (gethash form (build-normalized-originals build) form))))
    (cond (definition (authored-source-key build form))
          ((typep method 'sb-mop:standard-accessor-method)
           ;; The actual accessor specializer identifies its class declaration.
           (let ((class-form (loop for class in (sb-mop:method-specializers method)
                                   for source = (authored-class-form build class)
                                   when source return source)))
             (if class-form (authored-source-key build class-form)
                 (list (build-identity build) :generated-accessor generic))))
          (t (list (build-identity build) :host-method (method-logical-key build generic method))))))

(defun verify-standard-miss (build operation generic method)
  (let* ((gf (open-generic build generic))
         (applicable (sb-mop:compute-applicable-methods
                      (fdefinition operation) (if method (list gf method) (list gf))))
         (baseline (assoc operation *standard-miss-methods*))
         (selected (car applicable))
         (source (and selected (sb-introspect:find-definition-source (sb-mop:method-function selected))))
         (pathname (and source (sb-introspect:definition-source-pathname source))))
    (unless (and (= (length applicable) 1) (eq selected (second baseline))
                 (eq (sb-mop:method-function selected) (third baseline))
                 (typep pathname 'logical-pathname) (string= (host-namestring pathname) "SYS"))
      (fail build 'snowgrave:mop-failure :specialized-miss-protocol
            "A replaced or specialized miss method needs its own exact closed materialization." :materialization))
    t))

(defun emit-standard-miss (build operation generic method arguments)
  (verify-standard-miss build operation generic method)
  (audit-standard-generic-authority build generic)
  (let* ((nextp (eq operation 'no-next-method))
         ;; A computed list belongs to this one miss invocation. Bind it once
         ;; before condition/restart creation, preserving its identity and
         ;; keeping the retry closure independent of fixed dispatch receivers.
         (saved-arguments (unless (symbolp arguments) (fresh-name build "MISS-ARGUMENTS")))
         (actual-arguments (or saved-arguments arguments))
         (condition (if nextp 'sb-pcl::no-next-method-error 'sb-pcl::no-applicable-method-error))
         (expression `(error ',condition :generic-function #',(mapped-name generic (build-output-package build))
                             :method ',(when method (method-logical-key build generic method))
                             :args ,actual-arguments))
         (body (if nextp expression
                   `(restart-case ,expression
                      (sb-ext:retry () :report "Retry calling the generic function."
                        (apply #',(mapped-name generic (build-output-package build)) ,actual-arguments))))))
    (if saved-arguments `(let ((,saved-arguments ,arguments)) ,body) body)))

(defun emit-method-call (build generic method next-methods parameters)
  (when *initialization-phase*
    (return-from emit-method-call
      (emit-initialization-method-call build generic method next-methods parameters)))
  (when (and (eq generic 'shared-initialize)
             (eq method (second (assoc generic *standard-initialization-methods*))))
    (standard-initialization-method-p build generic method)
    (when next-methods (fail build 'snowgrave:mop-failure :shared-initialization-next
                             "The host shared initialization primary unexpectedly has next methods." :materialization))
    (return-from emit-method-call
      (values (emit-standard-shared-call build parameters) (make-return-summary (list :unknown) nil))))
  (multiple-value-bind (tail tail-proof)
      (when next-methods
        (emit-effective build generic `(call-method ,(car next-methods) ,(cdr next-methods)) parameters))
   (let* ((next-name (when tail (fresh-name build "NEXT")))
         (next-summary (if tail (let ((*effective-return-proof* t)) (form-return-summary build tail-proof)) :pending))
         (name (fresh-name build "METHOD"))
         (form (authored-method build generic method))
         (summary nil))
    (unless form
      (fail build 'snowgrave:unsupported-definition :method-provenance
            (format nil "The MOP method in generic ~S has no reproducible authored/accessor source." generic)
            :materialization))
    (with-build-source-key (build (method-source-key build generic method form))
    (push name (build-method-names build))
    (when next-name (push next-name (build-method-names build)))
    (when next-name (push `(defun ,next-name ,parameters ,tail) (build-generated build)))
    (multiple-value-bind (qualifiers lambda-list body) (method-parts form)
      (declare (ignore qualifiers))
      (let ((block-name (if (consp generic) (cadr generic) generic)))
        (let ((*argument-domains* nil) (*function-bindings* nil)
              (*local-function-frames* nil) (*value-domain-local-functions* nil)
              (*immediate-lambda-domains* nil)
              (*generated-class-operation*
               (or (typep method 'sb-mop:standard-accessor-method)
                   (and (eq generic 'initialize-instance)
                        (eq method (second (assoc generic *standard-initialization-methods*))))))
              (*current-method* (list generic method (not (null next-name)) next-summary)))
          (let ((domains (method-binding-domains build generic lambda-list body)))
          ;; Do not publish an UNKNOWN result while a caller's optional/key
          ;; fact is still pending. It would poison the monotone return join
          ;; before the same fixed point can discover the default's target.
          (setf summary (if (and *collect-function-flow* (member :pending domains)) :pending
                            (lambda-return-summary build lambda-list domains body :method t)))
          (multiple-value-bind (scope ordinary)
              (analyze-lambda-scope build lambda-list domains :package (build-output-package build)
                                   :method t :specials (body-special-domains body) :next next-name :original parameters)
            (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
              (push `(defun ,name ,parameters
                       ,(fixed-effective-method-body
                         build generic method ordinary
                         (append (when (source-specials build) (list `(declare (special ,@(source-specials build)))))
                                 (loop while (and body (consp (car body)) (eq (caar body) 'declare))
                                       collect (transform-form build (pop body) (build-output-package build)))
                                 (list `(block ,block-name
                                          ,@(transform-body build body (build-output-package build)
                                                            :next next-name :original parameters))))
                         parameters))
                    (build-generated build))))))))
    (values `(,name ,@parameters) (if (eq summary :pending) '(error) summary))))))

(defun emit-effective-call (build generic call parameters package local)
  (unless (and (snowgrave::source-finite-list-p call)
               (<= 2 (length call) 3)
               (snowgrave::source-finite-list-p (third call)))
    (fail build 'snowgrave:unsupported-definition :effective-method-call
          "CALL-METHOD requires one method and a literal finite next-method list." :materialization))
  (let ((method (second call)))
    (if (and (consp method) (eq (first method) 'make-method))
        (progn
          (unless (= (length method) 2)
            (fail build 'snowgrave:unsupported-definition :effective-method-call
                  "MAKE-METHOD requires exactly one effective body." :materialization))
          ;; Normalized in the surrounding CEM lexical environment, including
          ;; local macros. The shared transformer retains runtime bindings.
          (multiple-value-bind (code receipt)
              (transform-form build (second method) package :local local)
            (values code (or receipt (form-return-summary build (second method))))))
        ;; An authored method has its own definition environment; CALL-METHOD
        ;; syntax is not legal in its ordinary body.
        (let ((*effective-method-emitter* nil) (*flow-value-receipts* nil))
          (multiple-value-bind (code proof)
              (emit-method-call build generic method (third call) parameters)
            (let ((*effective-return-proof* t))
              (values code (form-return-summary build proof))))))))

(defun emit-effective (build generic form parameters)
  "Lower a CEM through the same lexical source and call-flow owners.
Only CALL-METHOD is composer syntax. Its ordinary code and typed result are
co-produced at the leaf's actual source evaluation point; no ambient authored
function cell or independent CEM source interpreter participates."
  (let* ((definition (authored-combination-name build (source-generic-combination build generic)))
         (source-key (if definition
                         (authored-source-key build (snowgrave:authored-definition-form definition))
                         (build-source-key build))))
    (with-build-source-key (build source-key)
      (let* ((*flow-value-receipts* nil)
             ;; Returned CEM code executes at runtime, but its macro expansion
             ;; is a repeated cold input and needs the same expander proof.
             (*reproducible-source-expansion* t)
             (*effective-method-emitter*
               (lambda (call package local)
                 (emit-effective-call build generic call parameters package local)))
             (normalized (normalize-source-expression build form)))
        (multiple-value-bind (code receipt)
            (transform-form build normalized (build-output-package build)
                            :local *value-domain-local-functions*)
          (let ((summary (or receipt (form-return-summary build normalized))))
            ;; Existing callers consume one typed proof leaf; an authored
            ;; literal :PENDING remains distinct from return-lattice bottom.
            (values code (if (eq summary :pending) '(error) summary))))))))

(defun generic-axis (build methods position)
  (let ((classes nil) (universal nil))
    ;; Universe roots are admitted even when no method specializes on them.
    ;; Their miss behavior is a real cell, never the violation fallback.
    (dolist (name (getf (build-declaration build) :universe))
      (if (eq name t) (setf universal t)
          (let ((root (find-class (if (member-name name (build-classes build))
                                    (mapped-name name (build-open-package build)) name) nil)))
            (unless root (fail build 'snowgrave:incomplete-domain :universe-root
                               "A universe root has no finalized class." :partition))
            (unless (or (member-name name (build-classes build)) (typep root 'built-in-class)
                        ;; SBCL models the native FUNCTION class as SYSTEM-CLASS.
                        (eq name 'function))
              (fail build 'snowgrave:incomplete-domain :universe-class-kind
                    "A native universe root needs a built-in class or the mapped FUNCTION class." :partition))
            (dolist (class (class-closure root))
              (when (or (member-name (source-class build class) (build-classes build))
                        (typep class 'built-in-class) (eq (sb-mop:class-name class) 'function))
                (pushnew class classes :test #'eq))))))
    (dolist (method methods)
      (let ((specializer (nth position (sb-mop:method-specializers method))))
        (when (typep specializer 'sb-mop:eql-specializer)
          (fail build 'snowgrave:unsupported-definition :eql-specializer
                "EQL cells require deployable identity and an exact class-remainder proof." :partition))
        (let ((name (sb-mop:class-name specializer)))
          (if (eq name t) (setf universal t)
              (progn
                (unless (or (member-name (source-class build specializer) (build-classes build))
                            (member-name name (getf (build-declaration build) :universe)))
                  (fail build 'snowgrave:incomplete-domain :built-in-specializer
                        (format nil "Non-universal specializer ~S must be explicit in :UNIVERSE." name) :partition))
                (dolist (class (class-closure specializer))
                  (when (or (member-name (source-class build class) (build-classes build))
                            (typep class 'built-in-class) (eq (sb-mop:class-name class) 'function))
                    (pushnew class classes :test #'eq))))))))
    (when universal (pushnew (find-class t) classes :test #'eq))
    (unless classes
      (fail build 'snowgrave:incomplete-domain :empty-axis
            "No proven argument classes can reach this generic." :partition))
    (sort classes (lambda (a b)
                    (let ((ac (length (sb-mop:class-precedence-list a)))
                          (bc (length (sb-mop:class-precedence-list b))))
                      (if (= ac bc)
                          (string< (symbol-name (sb-mop:class-name a))
                                   (symbol-name (sb-mop:class-name b))) (> ac bc)))))))

(defun cartesian-product (axes)
  (if (null axes) (list nil)
      (loop for head in (car axes)
            append (mapcar (lambda (tail) (cons head tail)) (cartesian-product (cdr axes))))))

(defun standard-class-applicability-p (generic)
  "The admitted stock protocol gives class-specializer independence.
Custom MOP methods keep the original concrete partition; no inferred purity or
class whitelist replaces their actual applicability behavior."
  (let* ((methods (sb-mop:compute-applicable-methods
                   #'sb-mop:compute-applicable-methods-using-classes (list generic nil)))
         (method (car methods))
         (source (and method (sb-introspect:find-definition-source (sb-mop:method-function method))))
         (pathname (and source (sb-introspect:definition-source-pathname source))))
    (and (= (length methods) 1)
         (eq method (first *standard-class-applicability-method*))
         (eq (sb-mop:method-function method) (second *standard-class-applicability-method*))
         (typep pathname 'logical-pathname) (string= (host-namestring pathname) "SYS"))))

(defun factor-universal-axes (generic methods concrete class-name)
  ;; This cold MOP step is independent of source namespace mapping.
  ;; Universal specialization cannot distinguish any classes on that axis.
  ;; Its representative stays T, including for method argument proof: the
  ;; caller's arbitrary value never borrows a narrower concrete class fact.
  (let* ((standardp (standard-class-applicability-p generic))
         (universal (find-class t))
         (folded (loop for axis in concrete for position from 0
                       when (and standardp methods (> (length axis) 1)
                                 (every (lambda (method)
                                          (eq (nth position (sb-mop:method-specializers method)) universal)) methods))
                         collect position)))
    (values (loop for axis in concrete for position from 0
                  collect (if (member position folded) (list universal) axis))
            (mapcar (lambda (position)
                      (list :position position :proof :standard-universal-specializer
                            :classes (mapcar class-name (nth position concrete)))) folded))))

(defun generic-partition-plan (build generic methods arity)
  ;; Still enumerate/validate every frozen class and specializer boundary.
  (let ((concrete (loop for position below arity collect (generic-axis build methods position))))
    (multiple-value-bind (axes evidence)
        (factor-universal-axes generic methods concrete (lambda (class) (source-class build class)))
      (values axes evidence concrete))))

(defun verify-universal-axes (build generic cell applicable evidence concrete)
  ;; Applicability/order independence follows from the unchanged stock MOP
  ;; and every actual specializer being T on this axis. Also recompute the
  ;; ordered list at every frozen concrete class. The same ordered list can
  ;; reuse this independence proof at another retained boundary tuple.
  ;; This is additive in universal axes, not their Cartesian product.
  (let ((replays 0))
   (dolist (axis evidence replays)
    (let ((position (getf axis :position)))
      (dolist (class (nth position concrete))
        (let ((probe (copy-list cell)))
          (setf (nth position probe) class)
          (incf replays)
          (multiple-value-bind (actual certainp)
              (sb-mop:compute-applicable-methods-using-classes generic probe)
            (unless (and certainp (equal applicable actual))
              (fail build 'snowgrave:mop-failure :universal-axis-uniformity
                    "The actual MOP changed applicability/order within a universal-specializer axis."
                    :partition)))))))))

(defun cell-test (build class parameter)
  (let ((source (source-class build class)))
    (cond ((eq source t) t)
          ((member-name source (build-classes build))
           ;; Exact class identity keeps every sealed concrete subclass in
           ;; exactly one cell, even with multiple inheritance.
           (record-layout-test build source parameter))
          (t (builtin-type-test build source parameter)))))

(defun record-layout-test (build class parameter)
  `(snowgrave:sg-record-matches-layout-p ,parameter ,(ensure-layout build class)))

(defun record-type-test (build class parameter)
  `(or ,@(loop for layout in (build-layouts build)
               when (member class (getf layout :ancestors))
                 collect (record-layout-test build (getf layout :class) parameter))))

(defun keyword-name (spec)
  (let ((head (if (consp spec) (car spec) spec)))
    (if (consp head) (car head) (intern (symbol-name head) :keyword))))

(defparameter *method-fast-function-reader* (fdefinition 'sb-pcl::safe-method-fast-function))

(defun method-positional-surplus-p (build method)
  "The native method binder determines optional error payload and timing."
  (unless (eq *method-fast-function-reader* (fdefinition 'sb-pcl::safe-method-fast-function))
    (fail build 'snowgrave:mop-failure :optional-method-parser-realization
          "The pinned native method realization reader has changed." :materialization))
  (let* ((function (funcall *method-fast-function-reader* method))
         (lambda-list (and function (sb-introspect:function-lambda-list function))))
    (unless (and function (snowgrave::source-finite-list-p lambda-list))
      (fail build 'snowgrave:mop-failure :optional-method-parser-realization
            "The optional method needs its native finite binding convention." :materialization))
    (not (null (member '&rest lambda-list)))))

(defvar *positional-surplus-schema* nil)

(defun positional-surplus-schema (build)
  "Verify the stock host's bounded optional parser without authored execution."
  (or *positional-surplus-schema*
      (let* ((gf (make-instance 'standard-generic-function :lambda-list '(object &optional value)))
             (prototype (sb-mop:class-prototype (find-class 'standard-method)))
             (marker :snowgrave-surplus-probe))
        (multiple-value-bind (source initargs)
            (sb-mop:make-method-lambda
             gf prototype '(lambda (object &optional value) (declare (ignore object value)) nil) nil)
          (add-method gf (apply #'make-instance 'standard-method :qualifiers nil
                                :lambda-list '(object &optional value)
                                :specializers (list (find-class t)) :function (compile nil source) initargs)))
        (let ((condition (handler-case (progn (funcall gf nil nil marker) nil)
                           (error (condition) condition))))
          (unless (and (eq (type-of condition) 'sb-int:simple-program-error)
                       (equal (simple-condition-format-arguments condition) (list (list marker)))
                       (equal (simple-condition-format-control condition) "surplus arguments: ~S"))
            (fail build 'snowgrave:mop-failure :optional-surplus-error-schema
                  "The stock optional parser needs its exact surplus-tail condition schema." :materialization))
          (setf *positional-surplus-schema*
                (list (type-of condition) (simple-condition-format-control condition)))))))

(defun emit-argument-validator (build generic gf applicable)
  (let* ((contract (generic-parser-contract build gf applicable))
         (name (fresh-name build "CONTRACT"))
         (required (mapcar (lambda (x) (declare (ignore x)) (fresh-name build "CHECK-ARG")) (getf contract :required)))
         (optional (mapcar (lambda (x) (declare (ignore x)) (fresh-name build "CHECK-OPT")) (getf contract :optional)))
         (finite-optional-p (and (getf contract :optional) (not (getf contract :rest)) (not (getf contract :keyp))))
         (rest (when (or (getf contract :rest) (getf contract :keyp)) (fresh-name build "CHECK-REST")))
         (keywords (getf contract :accepted-keywords))
         (allow (getf contract :allow)))
    (let* ((key-specs (when (getf contract :keyp)
                        (mapcar (lambda (key) (list (list key (fresh-name build "CHECK-KEY")))) keywords)))
           (all-variables (append required optional (when rest (list rest))
                                  (mapcar (lambda (spec) (cadar spec)) key-specs)))
           (lambda-list (append required (when optional (cons '&optional optional))
                                (when rest (list '&rest rest))
                                (when (getf contract :keyp) (cons '&key key-specs))
                                (when (and (getf contract :keyp) allow) '(&allow-other-keys)))))
      (unless finite-optional-p
        (push `(defun ,name ,lambda-list
                 ,@(when all-variables (list `(declare (ignore ,@all-variables))))
                 (values)) (build-generated build)))
      (values (unless finite-optional-p name) (list :generic generic :keywords keywords :allow-other-keys allow
                         :lambda-list lambda-list) contract))))

(defun emit-minimum-arity-check (build generic gf required established arguments)
  (when (plusp required)
    (let ((condition (handler-case (progn (funcall gf) nil) (error (condition) condition)))
          (name (fresh-name build "MINIMUM-CONTRACT"))
          (variables (loop repeat required collect (fresh-name build "CHECK-ARG")))
          (tail (fresh-name build "CHECK-REST")))
      ;; The fresh open generic has not been invoked by admitted initializers.
      ;; Too few arguments cannot enter an authored method or a miss protocol.
      ;; Capture its exact host error schema, including its generic reference.
      (unless (and (eq (type-of condition) 'sb-int:simple-program-error)
                   (equal (simple-condition-format-arguments condition) (list gf required)))
        (fail build 'snowgrave:mop-failure :minimum-arity-error-schema
              "The host minimum-arity path does not expose the admitted condition schema." :materialization))
      (push `(defun ,name (,@variables &rest ,tail)
               (declare (ignore ,@variables ,tail)) (values)) (build-generated build))
      `(when (< (length ,arguments) ,required)
         (if ,established (apply #',name ,arguments)
             (error ',(type-of condition)
                    :format-control ,(simple-condition-format-control condition)
                    :format-arguments (list #',(mapped-name generic (build-output-package build)) ,required)))))))

(defun emit-generic (build generic)
  (when (initialization-generic-p generic)
    (return-from emit-generic (emit-initialization-generic build generic)))
  (let* ((gf (fdefinition (mapped-name generic (build-open-package build))))
         (lambda-list (sb-mop:generic-function-lambda-list gf))
         (variables (ordinary-lambda-list build lambda-list))
         (parameters (mapcar (lambda (x) (declare (ignore x)) (fresh-name build "ARG")) variables))
         (arguments (fresh-name build "ARGUMENTS"))
         (fixed-arities (multiple-value-list (fixed-generic-arity build generic)))
         (fixed-arity (first fixed-arities))
         (maximum-arity (second fixed-arities))
         (optionalp (and fixed-arity (> maximum-arity fixed-arity)))
         (positional-parameters
           (append parameters (when optionalp
                                (loop repeat (- maximum-arity fixed-arity)
                                      collect (fresh-name build "OPTIONAL-ARG")))))
         (argument-count (when optionalp (fresh-name build "ARGUMENT-COUNT")))
         (effective-parameters (if optionalp (append positional-parameters (list argument-count arguments)) parameters))
         (fixed-convention (if optionalp (list arguments argument-count fixed-arity maximum-arity)
                               (not (null fixed-arity))))
         (error-arguments (if fixed-arity
                              (let ((*fixed-effective-arguments* fixed-convention))
                                (if optionalp (fixed-effective-error-arguments positional-parameters)
                                    `(or ,arguments (list ,@parameters))))
                              arguments))
         (established (fresh-name build "DISPATCH-ESTABLISHED"))
         (methods (sb-mop:generic-function-methods gf))
         ;; Required-only validators are identical for every method set. Keep
         ;; one ordinary lambda contract, rather than a copy in every cell.
         (fixed-validator (when (and fixed-arity (not optionalp))
                            (multiple-value-list (emit-argument-validator build generic gf nil))))
         (plan (multiple-value-list (generic-partition-plan build gf methods (length parameters))))
         (axes (first plan)) (axis-evidence (second plan)) (concrete-axes (third plan))
         (cells (cartesian-product axes)) (clauses nil) (descriptions nil) (summary :pending)
         (fixed-miss nil)
         (verified-lists (make-hash-table :test #'equal)) (uniformity-replays 0))
    (push `(defparameter ,established nil) (build-generated build))
    ;; SBCL's initial discriminator enters NO-APPLICABLE-METHOD before its
    ;; bounded maximum-arity check. After an applicable cell establishes the
    ;; discriminator, the native bounded call convention checks arity first.
    ;; This boolean preserves that observable error state; it never computes
    ;; or caches a method, combination or class at runtime.
    (validate-generic-protocol build generic gf)
    (dolist (cell cells)
      (let ((*cell-domains* (mapcar (lambda (class) (source-class build class)) cell))
            (*cell-axis-domains* (mapcar (lambda (axis)
                                           (mapcar (lambda (class) (source-class build class)) axis)) axes)))
       (multiple-value-bind (applicable certainp)
          (sb-mop:compute-applicable-methods-using-classes gf cell)
        (unless certainp
          (fail build 'snowgrave:mop-failure :applicability
                "The host cannot prove class-only applicability for this cell." :partition))
        (unless (gethash applicable verified-lists)
          (incf uniformity-replays
                (verify-universal-axes build gf cell applicable axis-evidence concrete-axes))
          (setf (gethash applicable verified-lists) t))
        (cond
          ((not (generic-cell-has-admitted-input-p build generic))
           (push (list :classes (mapcar (lambda (class) (source-class build class)) cell)
                       :behavior :unreachable-from-admitted-calls
                       :proof :settled-ordered-call-inputs
                       :methods (mapcar (lambda (method) (method-logical-key build generic method)) applicable))
                 descriptions))
          (t
            (if (null applicable)
                (progn
                  ;; A shared fixed miss function can serve several cells; each
                  ;; call site still needs its own actual-row feasibility proof.
                  (audit-standard-generic-authority build generic)
                  (when (and fixed-arity (null fixed-miss))
                    (setf fixed-miss (fresh-name build "STANDARD-MISS"))
                    (push fixed-miss (build-method-names build))
                    (push `(defun ,fixed-miss (,arguments)
                             ,(emit-standard-miss build 'no-applicable-method generic nil arguments))
                          (build-generated build)))
                  (let* ((contract (lambda-contract build lambda-list))
                         (validator (if fixed-arity (unless optionalp (first fixed-validator))
                                        (unless (or (getf contract :rest) (getf contract :keyp))
                                          (emit-argument-validator build generic gf nil)))))
                    (push `(,(cons 'and (mapcar (lambda (class parameter) (cell-test build class parameter)) cell parameters))
                             (progn
                               ,@(when validator `((when ,(if fixed-arity `(and ,arguments ,established) established)
                                                     (apply #',validator ,arguments))))
                               ,(if fixed-miss `(,fixed-miss ,error-arguments)
                                    (emit-standard-miss build 'no-applicable-method generic nil error-arguments)))) clauses))
                  (push (list :classes (mapcar (lambda (class) (source-class build class)) cell)
                              :methods nil :behavior :standard-no-applicable-method) descriptions))
            (multiple-value-bind (effective options)
                (sb-mop:compute-effective-method gf (sb-mop:generic-function-method-combination gf) applicable)
              (when options
                (fail build 'snowgrave:unsupported-definition :effective-method-options
                      "The normalized source emitter does not ignore MOP options." :materialization))
              (multiple-value-bind (validator argument-contract parser-contract)
                  (if (and fixed-arity (not optionalp)) (values-list fixed-validator)
                      (emit-argument-validator build generic gf applicable))
              (audit-generic-parser-inputs build generic parser-contract)
              (multiple-value-bind (code proof)
                  (let* ((*fixed-effective-arguments* fixed-convention)
                         (input (nth-value 1 (method-binding-domains build generic lambda-list nil))))
                    (call-with-record-flow-input
                     build input
                     (lambda (domains)
                       (declare (ignore domains))
                       (multiple-value-bind (code proof)
                           (if *initialization-phase*
                               (emit-initialization-plan build generic effective (if fixed-arity effective-parameters (list arguments)))
                               (emit-effective build generic effective (if fixed-arity effective-parameters (list arguments))))
                         (let* ((*effective-return-proof* t)
                                (result (form-return-summary build proof)))
                           (values code (if *initialization-phase* (publish-record-flow-summary result) result)))))))
                ;; The cell wrapper above has already consumed the CEM proof
                ;; tree. Merge its typed result once; bottom is not source syntax
                ;; and an authored literal :PENDING remains an ordinary value.
                (setf summary (merge-return-summaries build summary proof))
                (push `(,(cons 'and (mapcar (lambda (class parameter) (cell-test build class parameter))
                                           cell parameters))
                         (progn (setf ,established t)
                                ,@(when validator
                                    (list (if fixed-arity `(when ,arguments (apply #',validator ,arguments))
                                              `(apply #',validator ,arguments))))
                                ,code)) clauses))
              (push (list :classes (mapcar (lambda (class) (source-class build class)) cell)
                          :argument-contract argument-contract
                          :methods (mapcar (lambda (method)
                                             (list (source-method-qualifiers build generic method)
                                                   (mapcar (lambda (specializer) (source-class build specializer))
                                                           (sb-mop:method-specializers method)))) applicable))
                    descriptions)))))))))
    (when *collect-function-flow*
      (let* ((previous (gethash generic (build-function-returns build) :pending))
             (merged (merge-return-summaries build previous summary)))
        (unless (same-return-summary-p previous merged)
          (setf (gethash generic (build-function-returns build)) merged
                *function-flow-changed* t))))
    (when fixed-arity
      (push `(defun ,(fixed-generic-name build generic)
                 (,@effective-parameters ,@(unless optionalp (list arguments)))
               (declare (special ,established))
               (cond ,@(reverse clauses)
                     (t (snowgrave:sg-domain-violation ',(build-identity build) ',generic ,error-arguments))))
            (build-generated build)))
    (push `(defun ,(mapped-name generic (build-output-package build)) (&rest ,arguments)
             (declare (special ,established))
             ,@(when parameters (list (emit-minimum-arity-check build generic gf (length parameters) established arguments)))
             (let (,@(loop for parameter in positional-parameters for position from 0
                           collect `(,parameter (nth ,position ,arguments)))
                   ,@(when optionalp `((,argument-count (length ,arguments)))))
               ,(if fixed-arity `(funcall #',(fixed-generic-name build generic)
                                        ,@positional-parameters ,@(when optionalp (list argument-count)) ,arguments)
                    `(cond ,@(reverse clauses)
                           (t (snowgrave:sg-domain-violation ',(build-identity build) ',generic ,arguments))))))
          (build-generated build))
    (list :generic generic :lambda-list lambda-list
          :fixed-call-kernel (when fixed-arity (snowgrave::function-name-key (fixed-generic-name build generic)))
          :fixed-call-arities (when fixed-arity (list fixed-arity maximum-arity))
          :argument-precedence-order (sb-mop:generic-function-argument-precedence-order gf)
          :axis-uniformity axis-evidence
          :uniformity-replays uniformity-replays
          :cells (nreverse descriptions))))

(defun domain-test (build domain parameter)
  (cond ((eq domain t) t)
        ((graph-node-domain-p domain)
         (let ((row (graph-node-row build domain)))
           (unless row
             (fail build 'snowgrave:incomplete-domain :entry-domain
                   "An installed entry graph identity needs its captured node." :partition))
           `(eq ,parameter ,(graph-literal-reference build (getf row :source)))))
        ((and (consp domain) (eq (car domain) 'eql)) `(eql ,parameter ',(cadr domain)))
        ((member-name domain (build-classes build))
         (record-type-test build domain parameter))
        ((and (symbolp domain) (member-name domain (getf (build-declaration build) :universe)))
         (builtin-type-test build domain parameter))
        (t (fail build 'snowgrave:incomplete-domain :entry-domain
                 (format nil "No sealed class/EQL domain for ~S." domain) :partition))))

(defun seed-entry-function-domains (build)
  ;; Public required domains keep their nominal guard. Every nonrequired
  ;; binding may instead be omitted, so its default shares the same projection
  ;; used for an unknown APPLY tail. Revisit it as helper returns settle.
  (dolist (name (getf (build-declaration build) :entries))
    (let* ((form (ordinary-function-form build name))
           (domains (or (cdr (assoc name (build-graph-root-names build) :test #'name=))
                        (cadr (assoc name (getf (build-declaration build) :external-domains) :test #'name=)))))
      (with-build-source-key (build (authored-source-key build form))
        (unless (= (length (ordinary-lambda-list build (caddr form))) (length domains))
          (fail build 'snowgrave:incomplete-domain :entry-arity
                (format nil "Entry ~S needs one domain per required argument." name) :partition))
        (let* ((actual (call-lambda-domains build (caddr form) (copy-tree domains) t
                                            :specials (body-special-domains (cdddr form))))
               (input (if (graph-state-profile-p build) (make-call-record-flow-input build actual) actual)))
          (multiple-value-bind (previous presentp) (gethash name (build-function-domains build))
            (let ((merged (if presentp
                              (if (graph-state-profile-p build) (join-record-flow-inputs build previous input)
                                  (mapcar (lambda (old new) (merge-value-domains build old new)) previous actual))
                              input)))
              (unless (and presentp (same-record-flow-input-p previous merged))
                (setf (gethash name (build-function-domains build)) merged
                      *function-flow-changed* t)))))))))

(defun infer-function-domains (build)
  "Compute effective helper binding domains from every admitted source caller.
Analysis output is discarded; the ordinary generation pass repeats all source
and class audits with the fixed point. Unknown captures poison the proof."
  (let ((generated (build-generated build)) (constructors (build-constructors build))
        (method-names (build-method-names build)) (sequence (build-sequence build))
        (dependencies (build-dependencies build))
        (*collect-function-flow* t) (*function-flow-changed* nil)
        (*settled-method-roots* nil) (iterations 0))
    (when (graph-state-profile-p build) (prepare-graph-state-proof build))
    (setf (build-function-domains build) (make-hash-table :test #'equal)
          (build-function-returns build) (make-hash-table :test #'equal)
          (build-function-values build) (make-hash-table :test #'equal)
          (build-generic-call-shapes build) (make-hash-table :test #'equal))
    (unwind-protect
         (progn
           (seed-entry-function-domains build)
           (loop
             (incf iterations)
             (setf *function-flow-changed* nil)
             (when (graph-state-profile-p build) (begin-graph-field-iteration build))
             (seed-entry-function-domains build)
             ;; Each iteration is an analysis scratch generation. Keep only
             ;; the persistent domain/return facts across the fixed point,
             ;; rather than retaining every temporary method body and name.
             ;; Resetting the name supply also bounds interned output symbols
             ;; and makes constructor/method roots participate each time.
             (setf (build-generated build) generated (build-constructors build) constructors
                   (build-method-names build) method-names (build-sequence build) sequence
                   (build-dependencies build) dependencies)
             ;; Return summaries can now reach calls in methods and value
             ;; initializers. Repeat these roots with each expanded fixed point.
             (dolist (name (deployed-generics build)) (emit-generic build name))
             (dolist (form (build-forms build))
               (when (and (eq (defining-kind form) :global) (> (length form) 2))
                 (with-build-source-key (build (authored-source-key build form))
                   (let ((*immediate-lambda-domains* nil))
                     (transform-global-initializer build (caddr form) (build-output-package build))))))
             (dolist (form (build-forms build))
               (when (eq (defining-kind form) :function)
                 (multiple-value-bind (input reachedp) (gethash (cadr form) (build-function-domains build))
                   (when reachedp
                     (setf (build-source-key build)
                           (authored-source-key build form))
                     (multiple-value-bind (code additional ordinary)
                         (analyze-record-flow-function build form input)
                       (declare (ignore code ordinary))
                       (let* ((name (cadr form))
                              (previous (gethash name (build-function-returns build) :pending))
                              (merged (merge-return-summaries build previous additional)))
                         (unless (same-return-summary-p previous merged)
                           (setf (gethash name (build-function-returns build)) merged
                                 *function-flow-changed* t))))))))
             ;; An unsolved recursive component is not a usable type fact.
             ;; Widen it to unknown and propagate that fact before final audit.
             (unless *function-flow-changed*
               (settle-retained-callables build)
               (maphash (lambda (name domains)
                          (settle-record-field-cases build domains)
                          (when (member :pending (flow-input-domains domains))
                            (if (record-flow-input-p domains)
                                (setf (record-flow-input-domains domains)
                                      (substitute :unknown :pending (record-flow-input-domains domains)))
                                (setf (gethash name (build-function-domains build)) (substitute :unknown :pending domains)))
                            (setf *function-flow-changed* t))
                          (settle-return-summary build name)) (build-function-domains build))
               (maphash (lambda (name shapes)
                          (declare (ignore name))
                          (maphash (lambda (key domains)
                                     (settle-record-field-cases build domains)
                                     (when (member :pending (flow-input-domains domains))
                                       (if (record-flow-input-p domains)
                                           (setf (record-flow-input-domains domains)
                                                 (substitute :unknown :pending (record-flow-input-domains domains)))
                                           (setf (gethash key shapes) (substitute :unknown :pending domains)))
                                       (setf *function-flow-changed* t))) shapes))
                        (build-generic-call-shapes build))
               (dolist (name (deployed-generics build))
                 ;; An otherwise uncalled selected method can discover helper
                 ;; returns in the final root pass. Do not poison those still
                 ;; pending returns before that pass has had a chance to run.
                 (when (or *settled-method-roots*
                           (gethash name (build-generic-call-shapes build)))
                   (settle-return-summary build name)))
               (unless (or *function-flow-changed* *settled-method-roots*)
                 ;; Caller facts and unresolved caller components have now
                 ;; propagated. Revisit selected method roots with UNKNOWN
                 ;; only where no actual caller proof exists, using the same
                 ;; argument/return fixed point to retain their dependencies.
                 (setf *settled-method-roots* t *function-flow-changed* t)))
             (settle-construction-domains build)
             (unless *function-flow-changed* (settle-graph-field-envelopes build))
             (unless *function-flow-changed* (return)))
           (setf (build-function-flow-evidence build)
                 (list :method :finite-argument-binding-fixed-point :iterations iterations
                       :optional-domain-method :effective-call-site-bindings
                       :key-domain-method :first-occurrence-call-site-bindings
                       :rest-domain-method :actual-tail-origin-through-shared-lambda-owner
                       :variable-tail-domain-method :opaque-origin-in-raw-call-shape
                       :primary-return-method :monotone-normal-and-explicit-escape-union
                       :ordered-return-method :same-fixed-point-binding-position-union
                       :generic-return-method :same-emitted-effective-method-proof-tree
                       :generic-binding-method :raw-call-shapes-through-shared-lambda-owner
                       :callable-identity-facts :finite-named-source-target-unions
                       :retained-named-values
                       (sort (loop for name being the hash-keys of (build-function-values build)
                                   collect (snowgrave::function-name-key name))
                             #'string< :key #'prin1-to-string)
                       :unresolved-return-domain :unknown
                       :escaping-capture-domain :arbitrary-callers
                       :generic-call-bindings
                       (loop for name in (getf (build-declaration build) :closed-generics)
                             for shapes = (gethash name (build-generic-call-shapes build))
                             collect (list :generic-key (snowgrave::function-name-key name)
                                           :raw-call-shapes
                                           (sort (when shapes
                                                   (loop for key being the hash-keys of shapes using (hash-value domains)
                                                         collect (copy-tree (cons key (flow-input-domains domains)))))
                                                 #'string< :key #'prin1-to-string)))
                       :generic-returns
                       (loop for name in (getf (build-declaration build) :closed-generics)
                             collect (append (list :generic-key (snowgrave::function-name-key name))
                                             (return-summary-evidence (gethash name (build-function-returns build) :unknown))))
                       :functions
                       (sort (loop for name being the hash-keys of (build-function-domains build)
                                   using (hash-value input)
                                   for domains = (flow-input-domains input)
                                   for contract = (lambda-contract build (caddr (ordinary-function-form build name)))
                                   for required-count = (length (getf contract :required))
                                   for positional-count = (length (lambda-positional-variables contract))
                                   collect (append (list :function-key (snowgrave::function-name-key name)
                                                 :required-domains (copy-tree (subseq domains 0 required-count))
                                                 :optional-domains (copy-tree (subseq domains required-count positional-count))
                                                 :key-domains (mapcar (lambda (spec domain) (list (keyword-name spec) (copy-tree domain)))
                                                                      (getf contract :keys) (nthcdr positional-count domains))
                                                 :rest-domain (when (getf contract :rest)
                                                                (copy-tree (nth (1- (length domains)) domains))))
                                                   (return-summary-evidence (gethash name (build-function-returns build) :unknown))))
                             #'string< :key #'prin1-to-string))))
      (setf (build-generated build) generated (build-constructors build) constructors
            (build-method-names build) method-names (build-sequence build) sequence
            (build-dependencies build) dependencies))))

(defun emit-functions (build)
  (let ((entries (getf (build-declaration build) :entries)) (entry-records nil))
    (dolist (form (build-forms build))
      (setf (build-source-key build) (authored-source-key build form))
      (case (defining-kind form)
        (:function
         ;; Only the entry-reachable cohort is deployed. Global initializers,
         ;; selected methods, construction and captures also seed the shared
         ;; fixed point. An absent helper has no caller facts and must not
         ;; become an extra unaudited root merely because it was authored.
         ;; PRESENTP matters: a reached zero-argument helper has NIL domains.
         (when (nth-value 1 (gethash (cadr form) (build-function-domains build)))
           (let* ((name (cadr form)) (lambda-list (caddr form))
                  (input (gethash name (build-function-domains build)))
                  (domains (flow-input-domains input))
                  (*argument-domains* nil) (*function-bindings* nil)
                  (*local-function-frames* nil) (*value-domain-local-functions* nil)
                  (*immediate-lambda-domains* nil))
            (multiple-value-bind (body summary ordinary)
                (analyze-record-flow-function build form input)
              (declare (ignore summary))
             (when (member-name name entries)
               (audit-graph-entry-result build name)
               (when (and (or (build-classes build) (getf (build-declaration build) :closed-generics))
                          (some #'external-result-domain-p
                                (return-summary-domains (gethash name (build-function-returns build)))))
                 (fail build 'snowgrave:unclosed-call :external-result-escape
                       "An entry cannot publish an unclassified external result that may retain open cohort state." :reachability))
               (ordinary-lambda-list build lambda-list)
               (let ((domains (cadr (assoc name (getf (build-declaration build) :external-domains)
                                          :test #'name=))))
                 (unless (= (length (ordinary-lambda-list build lambda-list)) (length domains))
                   (fail build 'snowgrave:incomplete-domain :entry-arity
                         (format nil "Entry ~S needs one domain per required argument." name) :partition))
                 (let ((declarations (loop while (and body (consp (car body)) (eq (caar body) 'declare))
                                           collect (pop body))))
                   (setf body
                         `(,@declarations
                           (unless (and ,@(mapcar (lambda (domain variable) (domain-test build domain variable))
                                                 domains (ordinary-lambda-list build lambda-list)))
                             (snowgrave:sg-domain-violation ',(build-identity build) ',name (list ,@(ordinary-lambda-list build lambda-list))))
                           ,@body)))
                 (push (list :name name :definition-key (list (build-identity build) :entry (snowgrave::function-name-key name))
                             :code-key (snowgrave::function-name-key (mapped-name name (build-output-package build))) :lambda-list lambda-list
                             :domains domains :violation-key :signal) entry-records)))
             (push `(defun ,(mapped-name name (build-output-package build))
                      ,ordinary
                      ,@(preserve-source-block name body))
                   (build-generated build))))))
        (:global
         (let ((*immediate-lambda-domains* nil))
           (when (and (> (length form) 2) (member (cadr form) (source-specials build)))
             (audit-external-shared-value build (cadr form) (caddr form)))
           (push `(,(car form) ,(global-binding-name build (cadr form) (build-output-package build) nil)
                   ,@(when (> (length form) 2)
                       (cons (transform-global-initializer build (caddr form) (build-output-package build)) (cdddr form))))
                 (build-generated build))))))
    (nreverse entry-records)))

(defun emit-configuration-bindings (build entries)
  ;; Public wrappers capture this installation's roots at load time. The
  ;; ordinary entry keeps its source arity and identity guard in the artifact.
  (mapcar
   (lambda (entry)
     (let ((roots (assoc (getf entry :name) (build-graph-root-references build) :test #'name=)))
       (when roots
         (let ((name (fresh-name build "BOUND-CONFIGURATION")))
           (push `(defun ,name ()
                    (,(mapped-name (getf entry :name) (build-output-package build)) ,@(cdr roots)))
                 (build-generated build))
           (setf (getf entry :bound-code-key) (snowgrave::function-name-key name)
                 (getf entry :bound-lambda-list) nil
                 (getf entry :binding) :fixed-configuration))))
     entry)
   entries))

(defun configuration-metadata (build)
  (when (build-graph-root-names build)
    (list :roots (copy-tree (build-graph-root-names build))
          :native-manifest (graph-native-manifest build)
          :source-custody :exclusive-one-way-adoption-on-success
          :native-custody :installation-owner-maintains-geometry-and-aliases
          :record-custody :private-installed-copy
          :entry-binding :explicit-zero-argument-fixed-roots
          :implicit-generic-authority :possible-native-error-exposure-refused
          :installation :one-incarnation-per-identity)))

(defun residual-source-audit (build forms)
  (let ((seen (make-hash-table :test #'eq))
        (constant-states (make-hash-table :test #'eq)))
   (labels ((walk (value)
             (cond ((symbolp value)
                    (when (eq (symbol-package value) (build-open-package build))
                      (fail build 'snowgrave:residual-metaobject :builder-symbol
                            "A generated root references the disposable builder namespace." :residual-audit)))
                   ((or (consp value) (simple-vector-p value))
                    (unless (gethash value seen)
                      (setf (gethash value seen) t)
                      ;; Code can bind uninterned lexical names. Literal
                      ;; vector payload uses the stricter constant grammar;
                      ;; one shared memo prevents repeated suffix validation.
                      (when (and (simple-vector-p value) (not (serializable-tree-p value constant-states)))
                        (fail build 'snowgrave:residual-metaobject :builder-constant
                              "An emitted vector contains nonserializable process-local data." :residual-audit))
                      (if (consp value) (progn (walk (car value)) (walk (cdr value)))
                          (loop for part across value do (walk part)))))
                   ((not (serializable-tree-p value))
                    (fail build 'snowgrave:residual-metaobject :builder-constant
                          "An emitted form contains a nonserializable process-local object." :residual-audit)))))
    (walk forms)))
  t)

(defun compiled-code-linkage-references (build code)
  "Return actual named linkage operands, including permanent native names.
SBCL omits permanent CL names from retained fixups, so those alone cannot
establish the native callable boundary. This adapter currently maps x86-64
RIP and NIL-relative linkage operands and actual adjacent constant function-cell
loads; other machine ABIs and general register/stack dataflow need a mapping."
  #+(and x86-64 (not immobile-space))
  (declare (ignore build))
  #+(and x86-64 (not immobile-space))
  (let ((references nil)
        (state (sb-disassem:make-dstate)))
    (dolist (segment (sb-disassem::get-code-segments code))
     (let ((constant-register nil))
      (sb-disassem:map-segment-instructions
       (lambda (chunk instruction)
         (let ((printer (sb-disassem::inst-printer instruction)))
           (when printer
             (funcall printer chunk instruction nil state)
             ;; SAFE-FDEFN-FUN may read a literal symbol/FDEFN's function
             ;; slot directly, without a linkage operand or retained fixup.
             ;; The actual x86-64 cell VOP emits adjacent qword MOVs. Resolve
             ;; their real code constant and slot offset, not a quoted name's
             ;; unrelated fdefinition. Unrelated symbol constants remain atoms.
             (let* ((operands (sb-disassem::dstate-operands state))
                    (movp (and (eq (sb-disassem::inst-name instruction) 'sb-x86-64-asm::mov)
                               (= (sb-disassem::dstate-n-operands state) 2)))
                    (destination (and movp (aref operands 0)))
                    (source (and movp (aref operands 1)))
                    (address (and (consp source) (eq (cdr source) :qword) (car source)))
                    (next-constant nil))
               (when (and (sb-x86-64-asm::gpr-p destination)
                          (= (ldb (byte 2 1) (sb-x86-64-asm::reg-id destination)) 0)
                          (typep address 'sb-x86-64-asm::machine-ea)
                          (null (sb-x86-64-asm::machine-ea-index address)))
                 (when (and constant-register
                            (eql (sb-x86-64-asm::machine-ea-base address) (car constant-register))
                            (= (sb-x86-64-asm::machine-ea-disp address)
                               (- (ash sb-vm:fdefn-fun-slot sb-vm:word-shift) sb-vm:other-pointer-lowtag)))
                   (pushnew (cdr constant-register) references :test #'equal))
                 (when (eq (sb-x86-64-asm::machine-ea-base address) :rip)
                   (multiple-value-bind (object validp)
                       (sb-disassem::code-constant-value
                        (+ (sb-disassem:dstate-next-addr state) (sb-x86-64-asm::machine-ea-disp address)) state :absolute)
                     (when (and validp (or (symbolp object) (sb-kernel:fdefn-p object)))
                       (setf next-constant (cons (sb-x86-64-asm::reg-num destination) object))))))
               ;; Only the actual adjacent native pattern is interpreted;
               ;; never carry a guessed register value across another opcode.
               (setf constant-register next-constant))
             (dotimes (index (sb-disassem::dstate-n-operands state))
               (let* ((operand (aref (sb-disassem::dstate-operands state) index))
                      (address (if (consp operand) (car operand) operand)))
                 (when (and (typep address 'sb-x86-64-asm::machine-ea)
                            (null (sb-x86-64-asm::machine-ea-index address)))
                   (let* ((base (sb-x86-64-asm::machine-ea-base address))
                          (displacement (sb-x86-64-asm::machine-ea-disp address))
                          (absolute
                            (cond ((eq base :rip)
                                   (+ (sb-disassem:dstate-next-addr state) displacement))
                                  ((and (eql base sb-vm:card-table-reg) (minusp displacement))
                                   (+ sb-vm:nil-value displacement)))))
                     (when absolute
                       (let ((reference (sb-vm::linkage-addr->name absolute :abs)))
                         (when reference (pushnew reference references :test #'equal))))))))
             (setf (sb-disassem::dstate-n-operands state) 0))))
       segment state)))
    references)
  #-(and x86-64 (not immobile-space))
  (fail build 'snowgrave:residual-metaobject :unmapped-compiler-linkage
        "This SBCL machine ABI lacks an actual named-linkage operand mapping." :compiled-residual-audit))

(defun compiled-root-audit (build roots special-values)
  "Inspect actual SBCL callable constants/captures before publishing roots.
Native ordinary compiler intrinsics and the separately supplied record runtime
are named trust boundaries; declared external operations retain their behavior.
This is hosted compiled-root evidence, not target or whole-image admission."
  (let ((seen (make-hash-table :test #'eq))
        (code-seen (make-hash-table :test #'eq))
        (admitted-codes (make-hash-table :test #'eq))
        (functions 0) (closures 0) (constants 0)
        (boundaries nil) (root-key nil))
    (dolist (root roots)
      (when (and (compiled-function-p (cdr root)) (not (typep (cdr root) 'generic-function)))
        (setf (gethash (sb-kernel:fun-code-header (sb-kernel:%fun-fun (cdr root))) admitted-codes) t)))
    (labels
        ((bad (feature detail)
           (snowgrave::reject 'snowgrave:residual-metaobject :compiled-residual-audit feature detail
                              :source-key (build-source-key build)
                              :path (list (build-identity build) :compiled-root root-key)))
         (builder-name-p (name)
           (cond ((symbolp name) (eq (symbol-package name) (build-open-package build)))
                 ((consp name) (or (builder-name-p (car name)) (builder-name-p (cdr name))))))
         (native-function-p (function)
           (let* ((source (ignore-errors (sb-introspect:find-definition-source function)))
                  (pathname (and source (sb-introspect:definition-source-pathname source))))
             (and (typep pathname 'logical-pathname) (string= (host-namestring pathname) "SYS"))))
         (boundary (kind name)
           (pushnew (list kind name) boundaries :test #'equal))
         (function-boundary (function)
           (let ((name (sb-kernel:%fun-name (sb-kernel:%fun-fun function)))
                 (external (find-if (lambda (external)
                                      (and (fboundp external) (eq function (fdefinition external))))
                                    (getf (build-declaration build) :external-operations))))
             (when (builder-name-p name)
               (bad :compiled-builder-call "Compiled code calls or captures a disposable builder function."))
             (cond
               (external (boundary :declared-external external) t)
               ;; Ordinary core functions were compiled independently of the
               ;; builder. Their representation/error contracts are recorded
               ;; separately and still require target admission.
               ((and (eq function (cdr (assoc name *record-runtime-functions* :test #'equal)))
                     (not (typep function 'generic-function)))
                (boundary :record-runtime name) t)
               ((and (native-function-p function) (not (typep function 'generic-function)))
                (let ((intrinsic (find function *native-ordinary-functions* :key #'cdr :test #'eq)))
                  (when intrinsic
                    (boundary :native-ordinary-intrinsic (car intrinsic)) t))))))
         (walk-function (function)
           (unless (function-boundary function)
             (when (typep function 'generic-function)
               (bad :compiled-open-generic "An undeclared open generic is reachable from compiled roots."))
             (unless (compiled-function-p function)
               (bad :uninspectable-callable "A compiled root retains an uninspectable callable."))
             (unless (gethash (sb-kernel:fun-code-header (sb-kernel:%fun-fun function)) admitted-codes)
               (bad :undeclared-compiled-call
                    (format nil "Callable ~S outside emitted code, ordinary intrinsics and declared external operations is reachable."
                            (sb-kernel:%fun-name (sb-kernel:%fun-fun function)))))
             (incf functions)
             (when (sb-kernel:closurep function)
               (incf closures)
               (sb-impl::do-closure-values (value function :include-extra-values t) (walk value)))
             (let ((code (sb-kernel:fun-code-header (sb-kernel:%fun-fun function))))
               (unless (gethash code code-seen)
                 (setf (gethash code code-seen) t)
                 (sb-introspect::map-code-constants code (lambda (value) (incf constants) (walk value)))
                 ;; Normalize the native linkage seam: this SBCL can return
                 ;; an FDEFN as well as a name (including SETF). The contrib's
                 ;; public callee helper currently assumes names only.
                 (dolist (reference
                           (union (compiled-code-linkage-references build code)
                                  (mapcar (lambda (index) (sb-vm::linkage-addr->name index :index))
                                          (sb-c:unpack-code-fixup-locs (sb-vm::%code-fixups code)))
                                  :test #'equal))
                     (cond ((sb-kernel:fdefn-p reference) (walk reference))
                           (reference
                            (when (builder-name-p reference)
                              (bad :compiled-builder-linkage "A named compiled call belongs to the builder namespace."))
                            (unless (fboundp reference)
                              (bad :compiled-undefined-call
                                   (format nil "A named compiled call ~S has no admitted function binding." reference)))
                            (walk (fdefinition reference)))))))))
         (walk (object)
           ;; Terminal values have no executable edges. Do not retain a hash
           ;; entry for every distinct boxed scalar in a general native array.
           (unless (or (numberp object) (characterp object) (stringp object) (pathnamep object)
                       (gethash object seen))
             (setf (gethash object seen) t)
             (cond
               ((symbolp object)
                (when (builder-name-p object)
                  (bad :compiled-builder-symbol "A compiled constant refers to the disposable builder namespace."))
                ;; Names are logical atoms. Follow only the actual staged
                ;; source cells; symbol plists/unrelated function cells and
                ;; source classes are not executable references from a name.
                (let ((cell (assoc object special-values :test #'eq)))
                  (when (and cell (second cell)) (walk (third cell)))))
               ((consp object) (walk (car object)) (walk (cdr object)))
               ((functionp object) (walk-function object))
               ((sb-kernel:fdefn-p object)
                (when (builder-name-p (sb-kernel:fdefn-name object))
                  (bad :compiled-builder-fdefn "A compiled function cell belongs to the disposable builder namespace."))
                (let ((function (sb-kernel:fdefn-fun object)))
                  (unless function
                    (bad :compiled-undefined-call
                         (format nil "A compiled function cell ~S has no admitted function binding."
                                 (sb-kernel:fdefn-name object))))
                  (walk function)))
               ((typep object 'sb-kernel:layout)
                (let* ((classoid (sb-kernel:layout-classoid object))
                       (name (sb-kernel:classoid-name classoid)))
                  (when (or (builder-name-p name) (member-name name (build-classes build)))
                    (bad :compiled-authored-layout "A compiled type/layout constant still depends on an authored CLOS class."))
                  (unless (or (typep classoid 'sb-kernel:built-in-classoid)
                              (member name '(snowgrave::record-layout snowgrave::closed-record
                                             snowgrave::reference-domain snowgrave::reference-schema restart)))
                    (bad :unadmitted-layout
                         (format nil "A compiled layout for ~S lacks an ordinary representation contract." name)))
                  (boundary :ordinary-representation-layout name)))
               ((typep object 'sb-mop:metaobject)
                (bad :compiled-metaobject "A class, method, slot or combination object is reachable from compiled constants or captures."))
               ((snowgrave::record-layout-p object)
                (walk (snowgrave::record-layout-identity object))
                (walk (snowgrave::record-layout-class-identity object))
                (walk (snowgrave::record-layout-class object))
                (walk (snowgrave::record-layout-ancestors object))
                (walk (snowgrave::record-layout-slots object))
                (walk (snowgrave::record-layout-slot-types object))
                (walk (snowgrave::record-layout-row-token object))
                (walk (snowgrave::record-layout-reference-domain object))
                (walk (snowgrave::record-layout-reference-token object))
                (walk (snowgrave::record-layout-reference-class-index object))
                (walk (snowgrave::record-layout-reference-guards object))
                (walk (snowgrave::record-layout-error-mapping object)))
               ((snowgrave::reference-domain-p object)
                (walk (snowgrave::reference-domain-token object))
                (walk (snowgrave::reference-domain-schemas object))
                (walk (snowgrave::reference-domain-guards object)))
               ((snowgrave::reference-schema-p object)
                (walk (snowgrave::reference-schema-identity object))
                (walk (snowgrave::reference-schema-class object))
                (walk (snowgrave::reference-schema-ancestors object))
                (walk (snowgrave::reference-schema-slots object))
                (walk (snowgrave::reference-schema-slot-types object))
                (walk (snowgrave::reference-schema-error-mapping object)))
               ((snowgrave:sg-record-p object)
                (walk (snowgrave::closed-record-layout object))
                (walk (snowgrave::closed-record-values object))
                (walk (snowgrave::closed-record-bound object)))
               ((arrayp object)
                (let ((parent (array-displacement object))) (when parent (walk parent)))
                ;; Physical scalar storage cannot retain executable roots.
                ;; Still follow its backing allocation before this leaf check.
                (unless (snowgrave::native-scalar-array-storage-p object)
                  (dotimes (i (array-total-size object)) (walk (row-major-aref object i)))))
               ((packagep object)
                (when (eq object (build-open-package build))
                  (bad :compiled-builder-package "A compiled constant retains the builder package.")))
               (t (bad :uninspectable-constant
                       (format nil "A compiled constant of type ~S lacks a structural mapping." (type-of object))))))))
      (dolist (root roots)
        (setf root-key (snowgrave::function-name-key (car root)))
        (walk (cdr root)))
      (dolist (cell special-values)
        (when (second cell)
          (setf root-key (list :value-cell (snowgrave::function-name-key (first cell))))
          (walk (third cell))))
      (list :method :sbcl-boxed-code-closure-environments-and-named-callees
            :functions functions :closures closures :constant-edges constants
            :objects (hash-table-count seen)
            :scope :executable-constants-captures-and-published-values
            :named-call-method :x86-64-linkage-operands-retained-fixups-and-constant-function-cells
            :debug-roots-scanned nil :whole-image-roots-scanned nil
            :trust-boundaries (sort boundaries #'string< :key #'prin1-to-string)
            :builder-objects nil :target-accepted nil))))

(defun clean-package (package)
  (when package
    ;; Remove every method specialized on a disposable class, including
    ;; temporary host initialization methods, before detaching the namespace.
    (do-symbols (symbol package)
      (when (eq (symbol-package symbol) package)
        (let ((class (find-class symbol nil)))
          (when class
            (dolist (method (copy-list (sb-mop:specializer-direct-methods class)))
              (let ((generic (sb-mop:method-generic-function method)))
                (when generic (remove-method generic method))))
            (dolist (superclass (copy-list (sb-mop:class-direct-superclasses class)))
              (sb-mop:remove-direct-subclass superclass class))
            (setf (find-class symbol) nil)))
        (dolist (name (list symbol (list 'setf symbol)))
          (when (fboundp name)
            (let ((function (fdefinition name)))
              (when (typep function 'generic-function)
                ;; Native specializer direct-method lists are host roots.
                ;; Removing only the private fdefinition leaves builder
                ;; methods and their generic reachable from those roots.
                (dolist (method (copy-list (sb-mop:generic-function-methods function)))
                  (remove-method function method))))
            (fmakunbound name)))
        (when (boundp symbol)
          ;; These bindings belong exclusively to the discarded namespace.
          ;; Retire its compiler constant declaration before clearing its cell;
          ;; ordinary MAKUNBOUND must otherwise signal constant modification.
          (when (eq (sb-int:info :variable :kind symbol) :constant)
            (sb-int:clear-info :variable :kind symbol))
          (makunbound symbol))))
    (delete-package package)))

(defun validate-external-value-contracts (build)
  (let ((guards (getf (build-declaration build) :external-value-guards))
        (arguments (getf (build-declaration build) :external-argument-domains))
        (keys nil) (predicates nil) (names nil))
    (unless (and (serializable-tree-p guards) (snowgrave::source-finite-list-p guards))
      (fail build 'snowgrave:unsupported-definition :external-value-guard-contract
            "Installed value guards need finite stable (owner-key predicate native-structure-type) declarations." :declaration))
    (dolist (guard guards)
      (unless (and (snowgrave::source-finite-list-p guard) (= (length guard) 3)
                   (first guard) (serializable-tree-p (first guard))
                   (symbolp (third guard)) (not (member-name (third guard) (build-classes build)))
                   (let ((class (find-class (third guard) nil)))
                     (and class (eq (class-of class) (find-class 'sb-pcl::structure-class))))
                   ;; Importing the physical closed-record representation (or
                   ;; any parent/child of it) as "native" would erase the very
                   ;; logical interpretation this boundary must preserve.
                   (not (subtypep (third guard) 'snowgrave::closed-record))
                   (not (subtypep 'snowgrave::closed-record (third guard)))
                   (snowgrave::source-name-p (second guard))
                   (member-name (second guard) (getf (build-declaration build) :external-operations))
                   (not (member (first guard) keys :test #'equal)) (not (member-name (second guard) predicates))
                   (fboundp (second guard)) (not (typep (fdefinition (second guard)) 'generic-function))
                   (let ((lambda-list (sb-introspect:function-lambda-list (fdefinition (second guard)))))
                     (and (snowgrave::source-finite-list-p lambda-list) (= (length lambda-list) 1)
                          (symbolp (first lambda-list)) (not (member (first lambda-list) lambda-list-keywords))))
                   (equal '(boolean) (second (assoc (second guard)
                                                   (getf (build-declaration build) :external-return-domains) :test #'name=))))
        (fail build 'snowgrave:unsupported-definition :external-value-guard-contract
              "Each owner key/ordinary guard is unique with one BOOLEAN result and a native structure type disjoint from the standard-class cohort." :declaration))
      (push (first guard) keys) (push (second guard) predicates))
    (unless (and (serializable-tree-p arguments) (snowgrave::source-finite-list-p arguments))
      (fail build 'snowgrave:unsupported-definition :external-argument-contract
            "External required value tuples must form a finite stable declaration." :declaration))
    (dolist (contract arguments)
      (unless (and (snowgrave::source-finite-list-p contract) (= (length contract) 2)
                   (snowgrave::source-name-p (first contract))
                   (member-name (first contract) (getf (build-declaration build) :external-operations))
                   (not (member-name (first contract) names))
                   (not (member-name (first contract) predicates))
                   (snowgrave::source-finite-list-p (second contract))
                   (every (lambda (domain) (external-result-type-p build domain)) (second contract)))
        (fail build 'snowgrave:unsupported-definition :external-argument-contract
              "Each external has at most one native/guarded value tuple; a guard itself accepts all logical candidates." :declaration))
      (push (first contract) names))))

(defun validate-external-return-domains (build)
  "A declaration is an owner ABI obligation, never constructor inference.
Scalar/storage tuples and positively guarded unchanged owner values are
implemented here. A nominal native class is never an imported graph proof."
  (let ((contracts (getf (build-declaration build) :external-return-domains)) (seen nil))
    (unless (and (snowgrave::source-finite-list-p contracts) (serializable-tree-p contracts))
      (fail build 'snowgrave:unsupported-definition :external-return-contract
            "External result contracts must form a finite proper list." :declaration))
    (dolist (contract contracts)
      (unless (and (snowgrave::source-finite-list-p contract) (= (length contract) 2)
                   (snowgrave::source-name-p (first contract))
                   (member-name (first contract) (getf (build-declaration build) :external-operations))
                   (not (member-name (first contract) seen))
                   (snowgrave::source-finite-list-p (second contract))
                   (every (lambda (domain) (handler-case (external-result-type-p build domain) (error () nil)))
                          (second contract)))
        (fail build 'snowgrave:unsupported-definition :external-return-contract
              "Each declared external has at most one exact native/guarded returned tuple; nominal classes, callables and unguarded pointer graphs are not value ABIs." :declaration))
      ;; A native opaque constructor result never acquires an installed key
      ;; from its name or type alone. These return contracts may forward an
      ;; already guarded authority; a new value still needs its own guard.
      (labels ((keys (domain)
                 (cond ((external-value-domain-p build domain) (list (second domain)))
                       ((and (consp domain) (eq (car domain) 'or)) (mapcan #'keys (cdr domain))))))
        (let ((inputs (mapcan #'keys (second (assoc (first contract)
                                            (getf (build-declaration build) :external-argument-domains) :test #'name=)))))
          (dolist (key (mapcan #'keys (second contract)))
            (unless (member key inputs :test #'equal)
              (fail build 'snowgrave:unsupported-definition :external-value-return-contract
                    "An opaque returned owner key requires that same guarded authority in the operation's argument ABI." :declaration)))))
      (push (first contract) seen))))

(defun external-operation-records (build)
  (mapcar (lambda (name)
            (when (or (member-name name (build-functions build))
                      (member-name name (getf (build-declaration build) :closed-generics)))
              (fail build 'snowgrave:unsupported-definition :external-cohort-overlap
                    "An operation cannot simultaneously be external and part of the closed cohort." :declaration))
            (unless (fboundp name)
              (fail build 'snowgrave:unsupported-definition :external-operation-contract
                    (format nil "No ordinary lambda-list contract is available for external ~S." name) :declaration))
            (let ((lambda-list (sb-introspect:function-lambda-list (fdefinition name))))
              (unless lambda-list
                ;; NIL is also the exact lambda list of a zero-argument
                ;; function. SBCL introspection proves that case with its
                ;; explicit function type.
                (unless (let ((type (sb-introspect:function-type (fdefinition name))))
                          (and (consp type) (eq (car type) 'function) (null (cadr type))))
                  (fail build 'snowgrave:unsupported-definition :external-operation-contract
                        (format nil "External ~S has no inspectable lambda list." name) :declaration)))
              (let ((contract (assoc name (getf (build-declaration build) :external-return-domains) :test #'name=)))
                (list :identity name :lambda-list lambda-list
                      :argument-representation (if (find name (getf (build-declaration build) :external-value-guards)
                                                        :key #'second :test #'name=)
                                                   :identity-guarded-logical-candidates :proved-native-or-installed-values)
                      :required-value-domains (copy-tree (second (assoc name
                                                  (getf (build-declaration build) :external-argument-domains) :test #'name=)))
                      :result-representation (if contract :declared-native-value-domains :unclassified)
                      :returned-value-domains (when contract (copy-tree (second contract)))
                      :returned-value-count-complete-p (not (null contract))))))
          (getf (build-declaration build) :external-operations)))

(defun declare-closed-specials (form specials)
  (cond ((eq (car form) 'defun)
      (let ((body (cdddr form)))
        (list* 'defun (cadr form) (caddr form)
               (append (when (stringp (car body)) (list (pop body)))
                       (when specials (list `(declare (special ,@specials)))) body))))
        ;; Method lambda-list defaults precede the method body declaration.
        ;; Supply the lexical declaration around the defining macro too,
        ;; without globally proclaiming or initializing the source cell.
        ((and specials (member (car form) '(cl:defclass cl:defmethod)))
         `(locally (declare (special ,@specials)) ,form))
        (t form)))

(defun order-closed-definitions (build forms)
  ;; Ordinary dispatch definitions contain direct calls to static methods,
  ;; so installing them does not need the method functions yet. Methods can
  ;; contain LOAD-TIME-VALUE captures of those generics or authored helpers.
  ;; Install cold descriptor cells before their dispatchers, and method bodies
  ;; last so captures see the fresh ordinary bindings from the open CLOS pass.
  (labels ((rank (form)
             (cond ((and (eq (car form) 'defparameter)
                         (or (eq (second form) (build-graph-resource-name build))
                             (find (second form) (build-graph-imports build)
                                   :key (lambda (binding) (getf (cdr binding) :name))))) -1)
                   ((and (eq (car form) 'defparameter)
                         (or (eq (second form) (build-reference-domain-name build))
                             (member (second form) (build-layout-names build) :key #'cdr))) 0)
                   ((and (eq (car form) 'defun)
                         (some (lambda (generic)
                                 (equal (cadr form) (mapped-name generic (build-output-package build))))
                               (getf (build-declaration build) :closed-generics))) 1)
                   ((and (eq (car form) 'defun) (member (cadr form) (build-method-names build))) 3)
                   (t 2))))
    (stable-sort (copy-list forms) #'< :key #'rank)))

(defun publish-special-values (values)
  ;; Initializers have already run under PROGV and every audit has passed.
  ;; Their source identities stay shared, so ordinary dynamic binding by an
  ;; authored caller observes the same special variables as the closed code.
  (dolist (entry values)
    (proclaim `(special ,(first entry)))
    (if (second entry) (setf (symbol-value (first entry)) (third entry))
        (makunbound (first entry)))))

(defun layout-metadata (description)
  ;; Initializer expressions are compiler inputs; their executable behavior
  ;; is already in the emitted constructors. Keep provenance keys in the ABI,
  ;; rather than duplicating mutable/non-readable literal graphs as metadata.
  (let ((result (copy-list description)))
    (setf (getf result :slot-initializer-keys)
          (mapcar (lambda (initializer) (getf initializer :source-key))
                  (getf description :slot-initforms))
          (getf result :default-initializer-keys)
          (mapcar (lambda (initializer) (list (car initializer) (getf (cddr initializer) :source-key)))
                  (getf description :default-initargs)))
    (remf result :slot-initforms)
    (remf result :default-initargs)
    (remf result :construction-protocol)
    result))

(defun close-source (source declaration)
  (unless (serializable-tree-p (getf declaration :unit-name))
    (snowgrave::reject 'snowgrave:nonreproducible-source :declaration :unit-identity
                      "Unit identity must contain stable readable scalar/list data."))
  ;; Each invocation owns its proof environment, including a nested close
  ;; triggered by compile-time source processing. Dynamic binding restores the
  ;; outer build's facts; clearing an ambient cell would corrupt that build.
  (let* ((*argument-domains* nil) (*cell-domains* nil) (*function-bindings* nil)
         (*generated-class-operation* nil) (*current-method* nil)
         (*effective-return-proof* nil) (*effective-method-emitter* nil) (*fixed-effective-arguments* nil)
         (*active-construction-classes* nil) (*initialization-phase* nil) (*initialization-next* nil) (*initialization-plan* nil)
         (*flow-value-receipts* nil) (*flow-input-row* nil)
         (*flow-unknown-effect* nil) (*flow-deferred-call-p* nil) (*flow-exit-receipts* nil)
         (*flow-record-origins* nil) (*flow-defer-source-call* nil)
         (*collect-function-flow* nil) (*function-flow-changed* nil) (*settled-method-roots* nil)
         (*immediate-callee-value* nil) (*value-domain-local-functions* nil)
         (*local-function-frames* nil) (*local-function-scope-cache* nil)
         (*declared-specials* nil) (*mutable-invariant-bindings* nil) (*tagbody-targets* nil)
         (*immediate-lambda-domains* nil) (*cold-global-initializer* nil) (*cold-method-combination-factory* nil)
         (*cold-recipe-source-nodes* nil) (*cold-recipe-source-marker* nil)
         (*cold-recipe-normalization* nil) (*reproducible-source-expansion* nil)
         (*cold-recipe-active* nil) (*cold-recipe-functions* nil)
         (identity (getf declaration :unit-name))
         (identity-key (with-standard-io-syntax (write-to-string identity)))
         (open (make-package (format nil "SNOWGRAVE.BUILDER.~D" (incf *builder-counter*)) :use '(:cl)))
         (output-name (format nil "SNOWGRAVE.UNIT.~A" identity-key))
         (build (make-build :identity (snowgrave::immutable-copy identity) :declaration declaration :open-package open))
         (published nil))
    (unwind-protect
         (progn
           (unless (serializable-tree-p identity)
             (fail build 'snowgrave:nonreproducible-source :unit-identity
                   "Unit identity must contain stable readable scalar/list data." :declaration))
           (when (or (gethash identity-key *published-identities*) (find-package output-name))
             (fail build 'snowgrave:unsupported-definition :sealed-identity
                   "A published unit identity cannot be reopened or reused." :declaration))
           (setf (build-source build)
                 (snowgrave:make-authored-source (read-source source) :identity identity
                                                :copy-observer (source-copy-observer build)))
           (index-source build)
           (normalize-authored-source build)
           (validate-external-value-contracts build)
           (validate-external-return-domains build)
           (compile-forms build
                          (with-literal-pool build
                            (mapcar (lambda (form) (declare-closed-specials (open-definition build form) (source-specials build)))
                                    (build-forms build)) open)
                          :open-pass :stage-specials (source-specials build))
           (obtain-layouts build)
           (when (entry-rooted-deployment-p build) (audit-sealed-generic-provenance build))
           (setf (build-output-package build) (make-package output-name :use '(:cl)))
           ;; Shared type data is persistent generation state. Establish it
           ;; before the return-domain fixed point takes/discards scratch
           ;; emissions, so a cached name can never outlive its definition.
           (ensure-admitted-layouts build)
           (when (entry-graph-request-p build) (capture-entry-graph build))
           (infer-function-domains build)
           (let* ((dispatch (mapcar (lambda (name) (emit-generic build name))
                                    (deployed-generics build)))
                  (entries (emit-configuration-bindings build (emit-functions build)))
                  (specials (source-specials build))
                  (forms (with-literal-pool build
                           (order-closed-definitions
                            build (mapcar (lambda (form) (declare-closed-specials form specials))
                                          (nreverse (build-generated build))))
                           (build-output-package build)))
                  (metadata (list :abi-version 3 :identity identity :entries entries
                                  :deployment (deployment-evidence build)
                                  :cold-integer-constants (cold-integer-constant-evidence build)
                                  :configuration (configuration-metadata build)
                                  :source-normalization
                                  '(:method :sbcl-lexical-host-macroexpansion
                                    :snapshot :once-per-authored-definition
                                    :pass-input :owned-sharing-preserving-graph
                                    :source-keys :authored-definition-position)
                                  :reference-domain (when (build-reference-domain-name build)
                                                      (list :identity identity :schema-source :record-layouts))
                                  :record-layouts (mapcar #'layout-metadata (build-layouts build)) :dispatch dispatch
                                  :definitions (loop for form in forms when (eq (car form) 'defun)
                                                     collect (list :definition-key (list identity :definition
                                                                                         (snowgrave::function-name-key
                                                                                          (or (find-if (lambda (name)
                                                                                                        (equal (mapped-name name (build-output-package build)) (cadr form)))
                                                                                                       (append (build-functions build) (getf declaration :closed-generics)))
                                                                                              (cadr form))))
                                                                   :code-key (snowgrave::function-name-key (cadr form))
                                                                   :lambda-list (caddr form)))
                                  :external-operations (external-operation-records build)
                                  :external-value-guards
                                  (mapcar (lambda (guard)
                                            (list :owner-key (copy-tree (first guard)) :predicate (second guard)
                                                  :native-structure-type (third guard)
                                                  :cohort-disjointness :native-structure-outside-record-runtime
                                                  :candidate-abi :all-logical-values-by-identity
                                                  :positive-abi :unchanged-installed-value
                                                  :lifetime :external-installation-owner))
                                          (getf declaration :external-value-guards))
                                  :ordinary-function-flow (build-function-flow-evidence build)))
                  (report (list :implementation :snowgrave-sbcl :claim :semantically-closed
                                :deployment (deployment-evidence build)
                                :cold-integer-constants (cold-integer-constant-evidence build)
                                :fragment :standard-method-and-authored-initialization-contracts
                                :declaration (snowgrave::immutable-copy declaration)
                                :argument-forwarding :whole-original-argument-list
                                :keyword-validator :fresh-host-ordinary-lambda-list
                                :construction :materialized-authored-initialization
                                :ordinary-function-flow (build-function-flow-evidence build)
                                :function-type-observation :native-types-with-exact-closed-generic-identities
                                :direct-initialization :literal-keywords-and-slot-selections
                                :error-mappings '(:minimum-arity :same-host-initial-and-established-conditions
                                                  :slot-errors :ordinary-hosted-layout-descriptor-and-restarts
                                                  :keyword-errors :same-host-parser
                                                  :invalid-initargs :same-host-condition-with-exact-class-token
                                                  :no-next-method :same-host-condition-with-logical-method-key
                                                  :no-applicable-method :same-host-condition-and-retry
                                                  :miss-arity-state :initial-and-established-sbcl-discriminator)
                                :audit :source-and-compiled-structural
                                :source-admitted t :second-pass-fresh t :residual-source-audited t
                                :target-accepted nil :differential-validated nil :matrix-rows nil
                                :mop-layer :sb-mop-source-normalization
                                :dependencies (sort (copy-list (build-dependencies build))
                                                                       #'string< :key #'prin1-to-string))))
             (residual-source-audit build forms)
             (let ((special-values (compile-forms build forms :closed-pass :stage-specials specials)))
              (setf (getf report :compiled-root-evidence)
                    (compiled-root-audit
                     build
                     (loop for form in forms when (eq (car form) 'defun)
                           collect (cons (cadr form) (fdefinition (cadr form))))
                     (append special-values
                             (loop for form in forms
                                   when (and (member (car form) '(defparameter defvar))
                                             (not (member (cadr form) specials)))
                                     collect (list (cadr form) (boundp (cadr form))
                                                   (when (boundp (cadr form)) (symbol-value (cadr form))))))))
              (unless (serializable-tree-p (getf report :compiled-root-evidence))
                (fail build 'snowgrave:residual-metaobject :compiled-dependency-identity
                      "A compiled dependency lacks a stable readable identity." :compiled-residual-audit))
              (setf (getf metadata :compiler-dependencies)
                    (getf (getf report :compiled-root-evidence) :trust-boundaries))
              (dolist (name (deployed-generics build))
               (when (typep (fdefinition (mapped-name name (build-output-package build))) 'generic-function)
                 (fail build 'snowgrave:residual-metaobject :generic-root
                       "The second-pass generic binding remains open." :residual-audit)))
             (let ((unit (snowgrave::%make-unit
                          :metadata metadata :source forms :report report
                          :bindings (mapcar (lambda (name)
                                              (cons (snowgrave::function-name-key name)
                                                    (fdefinition (mapped-name name (build-output-package build)))))
                                            (getf declaration :entries))
                          :configuration-bindings
                          (loop for entry in entries for key = (getf entry :bound-code-key)
                                when key collect
                                  (cons (snowgrave::function-name-key (getf entry :name))
                                        (fdefinition (intern (second key) (first key))))))))
               (publish-special-values special-values)
               (setf (gethash identity-key *published-identities*) t published t)
               unit))))
      (clean-package open)
      (unless published (clean-package (build-output-package build))))))

(snowgrave:register-source-adapter :sbcl #'close-source)
