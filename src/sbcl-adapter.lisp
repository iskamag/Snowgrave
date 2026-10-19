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
(defvar *function-bindings* nil)
(defvar *generated-class-operation* nil)
(defvar *current-method* nil)
(defvar *effective-return-proof* nil)
(defvar *fixed-effective-arguments* nil)
(defvar *collect-function-flow* nil)
(defvar *function-flow-changed* nil)
(defvar *immediate-function-reference* nil)
(defvar *value-domain-local-functions* nil)
(defvar *declared-specials* nil)
(defvar *mutable-invariant-bindings* nil)
(defvar *tagbody-targets* nil)
(defvar *immediate-lambda-domains* nil)

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
  (sequence 0) (dependencies nil) (source-key nil)
  (literal-pools nil)
  (literal-states (make-hash-table :test #'eq))
  function-domains function-returns generic-call-shapes function-flow-evidence)

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
           (cond
             ((or (not (eq context :eval)) (atom form)) form)
             ((and (member (car form) '(macrolet symbol-macrolet)) (not (eq form wrapper)))
              ;; Let the host establish the local definitions, then discard
              ;; compile-time wrappers. Their expanded executable bodies are
              ;; the only inputs to either materialization pass.
              (let* ((previous wrapper)
                     (normalized (unwind-protect (progn (setf wrapper form) (walk form env))
                                   (setf wrapper previous))))
                (values `(locally ,@(cddr normalized)) t)))
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

(defun normalize-authored-source (build)
  ;; Neither a user expander that destructively edits its argument nor a
  ;; returned, globally aliased expansion can mutate the authored provenance
  ;; or the pass-two input. Own both graphs, preserving literal EQ sharing.
  (let* ((originals (snowgrave:authored-source-forms (build-source build)))
         (inputs (snowgrave::immutable-copy originals))
         (expanded (loop for original in originals for input in inputs
                         collect (with-build-source-key (build (authored-source-key build original))
                                   (normalize-authored-definition build input))))
         (frozen (snowgrave::immutable-copy expanded)))
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
  "Only required-only generic and method contracts can omit a raw argument list.
The actual MOP still selects and combines all methods. Optional, rest and key
contracts retain their complete ordinary argument path. AUX stays method-local."
  (when (and (member-name name (getf (build-declaration build) :closed-generics))
             (not (initialization-generic-p name)))
    (let ((gf (open-generic build name)))
      (labels ((fixedp (lambda-list &optional method)
                 (let ((contract (lambda-contract build lambda-list :method method)))
                   (not (or (getf contract :optional) (getf contract :rest)
                            (getf contract :keyp))))))
        (when (and (fixedp (sb-mop:generic-function-lambda-list gf))
                   (every (lambda (method) (fixedp (sb-mop:method-lambda-list method)))
                          (sb-mop:generic-function-methods gf)))
          (length (ordinary-lambda-list build (sb-mop:generic-function-lambda-list gf))))))))

(defun fixed-generic-name (build name)
  (if (consp name) (list 'setf (fixed-generic-name build (cadr name)))
      (intern (concatenate 'string "%FIXED-GENERIC/"
                           (with-standard-io-syntax
                             (write-to-string (snowgrave::function-name-key name))))
              (build-output-package build))))

(defun direct-call-name (build name package open local argument-count)
  ;; Resolve/audit the public binding before choosing its internal convention.
  ;; FUNCTION captures still use TRANSFORMED-FUNCTION-NAME and keep identity.
  (let ((public (transformed-function-name build name package open local))
        (arity (unless (or open (member-name name local)) (fixed-generic-arity build name))))
    (if (and arity (= arity argument-count))
        (values (fixed-generic-name build name) t) (values public nil))))

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
    ceiling truncate round ash logand logior logxor lognot evenp oddp
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

(defparameter *representation-sensitive-ordinary-operations*
  ;; These standard operators observe logical values or invoke callbacks. Their
  ;; contract follows the actual finite callee, independent of call syntax.
  '(gethash remhash make-hash-table mapcar mapc maplist mapcan reduce remove-if
    delete-if sort stable-sort member assoc find position count remove delete
    format princ prin1 print fill coerce))

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
                             sb-impl::vector-reverse
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
  (unless (function-target-p build name local)
    (fail build 'snowgrave:unclosed-call :call-target
          (format nil "Call or function capture of undeclared operation ~S." name)))
  (pushnew (snowgrave::function-name-key name) (build-dependencies build) :test #'equal)
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

(defun external-result-domain-p (domain)
  (or (eq domain :external-result)
      (and (consp domain) (eq (car domain) 'or) (some #'external-result-domain-p (cdr domain)))))

(defun external-value-domain-p (build domain)
  "An unchanged value established by an actual installed-owner predicate.
The stable key names its owner obligation, never a class or slot type."
  (and (consp domain) (eq (car domain) :external-value)
       (snowgrave::source-finite-list-p domain) (= (length domain) 2)
       (assoc (second domain) (getf (build-declaration build) :external-value-guards) :test #'equal)))

(defun external-value-observation-p (build domain)
  (or (external-value-domain-p build domain)
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

(defun native-data-domain-p (build domain)
  (or (external-value-domain-p build domain)
      (and (consp domain) (eq (car domain) 'or)
           (every (lambda (part) (native-data-domain-p build part)) (cdr domain)))
      (and (consp domain) (eq (car domain) 'eql)
           (or (numberp (cadr domain)) (symbolp (cadr domain)) (characterp (cadr domain))))
      (native-value-type-p domain)
      (and (not (eq domain :unknown))
           (or (subtype-domain-p build domain 'number) (subtype-domain-p build domain 'symbol)
               (subtype-domain-p build domain 'string) (subtype-domain-p build domain 'character)))))

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
       (getf (build-declaration build) :external-operations)
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
  (when (and (not *collect-function-flow*)
             (or (build-classes build) (getf (build-declaration build) :closed-generics))
             (external-result-domain-p (value-domain build value)))
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

(defun validate-callback (build reference arity local open
                          &key (data nil data-p) equalp-realization)
  (let* ((literal (cond ((and (consp reference) (eq (car reference) 'function)) (cadr reference))
                        ((and (consp reference) (eq (car reference) 'lambda)) reference)
                        ((and (consp reference) (eq (car reference) 'load-time-value)) (function-expression-target reference))
                        ((symbolp reference) (resolved-function build reference))))
         (names (or (known-function-targets build reference)
                    (when (and literal (not (eq literal :unknown))) (list literal)))))
    (when (special-variable-p build reference)
      (fail build 'snowgrave:unclosed-call :mutable-callback-special
            "The higher-order call cannot prove a mutable special's binding domain."))
    ;; A helper's returned callback may be pending during the shared fixed
    ;; point. The final emission must prove every target; inference itself
    ;; only walks the reference to collect its actual helper inputs/returns.
    (unless (or open names *collect-function-flow*)
      (fail build 'snowgrave:unclosed-call :callback-target
            "A higher-order operation needs a checked capture or complete finite named callback domain."))
    (dolist (name names)
     (unless (or open (member-name name local))
      (audit-external-identity build name data :variable-tail (not data-p))
      (when (and (not *collect-function-flow*)
                 (member-name name (getf (build-declaration build) :external-operations))
                 (not (and data-p (every (lambda (argument) (native-data-form-p build argument)) data))))
        (fail build 'snowgrave:unclosed-call :external-callback-representation
              "An external callback needs native element/accumulator/keyword value proofs or an admitted logical ABI." :reachability))
      (when (member-name name (getf (build-declaration build) :closed-generics))
        (let ((roots (generic-domain-roots build name)))
          (unless (and (>= arity (length roots)) (every (lambda (axis) (member t axis)) roots))
            (fail build 'snowgrave:incomplete-domain :callback-argument-domain
                  "A specialized higher-order callback needs sequence-element/reachability proof." :reachability))))
      (when (and (not *collect-function-flow*) (eq name 'equalp) (build-classes build)
                 (not equalp-realization))
        (fail build 'snowgrave:unclosed-class-operation :equalp-callback
              "Native EQUALP recursively observes lowered record structure; this callback needs an exact equality lowering."))
      (when (member name *representation-sensitive-ordinary-operations*)
        ;; The sequence data's native-tree proof also covers its elements;
        ;; opaque element shapes do not become safe merely through a callback.
        (audit-ordinary-operation build name data local open :variable-tail (not data-p)))))))

(defun validate-keyword-callbacks (build tail local open &optional equalp-realization)
  (unless (and (evenp (length tail))
               (loop for rest on tail by #'cddr always (keywordp (car rest))))
    (fail build 'snowgrave:unclosed-call :callback-target
          "Callback keywords need literal names and a complete ordered argument shape."))
  (when (and equalp-realization
             (loop for rest on tail by #'cddr thereis (eq (car rest) :test))
             (loop for rest on tail by #'cddr thereis (eq (car rest) :test-not)))
    (fail build 'snowgrave:unclosed-call :conflicting-equality-tests
          "Simultaneous TEST and TEST-NOT need the ordinary operator's exact error contract."))
  (loop with seen = nil
        for rest on tail by #'cddr for index from 1 by 2
        when (member (car rest) '(:test :test-not :key))
          do (unless (and (eq (car rest) :key) (null (cadr rest)))
               (validate-callback build (cadr rest) (if (eq (car rest) :key) 1 2) local open
                                  :equalp-realization (and (not (eq (car rest) :key)) equalp-realization)))
        when (and (not (member (car rest) seen))
                  (member (car rest) '(:test :test-not))
                  (eq equalp-realization :identity)
                  (member 'equalp (known-function-targets build (cadr rest))))
          collect index
        when (member (car rest) '(:test :test-not))
          do (pushnew (car rest) seen)))

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
      (values (cond ((external-result-domain-p input) :external-result)
                    ((and constantp (coerce-sequence-target-p target)) target)
                    (t :unknown)) t))))

(defun ordinary-call-argument-plan (build form)
  "Use the existing ordered producer owner for every MVC tuple."
  (case (car form)
    (funcall (values (cddr form) nil t))
    (apply
     (let ((tail (car (last form))))
       (cond ((and (consp tail) (eq (car tail) 'list))
              (values (append (butlast (cddr form)) (cdr tail)) nil t))
             ((and (consp tail) (eq (car tail) 'quote)
                   (snowgrave::source-finite-list-p (second tail)))
              (values (append (butlast (cddr form))
                              (mapcar (lambda (value) (list 'quote value)) (second tail))) nil t)))))
    (multiple-value-call
     (multiple-value-bind (arguments bindings domains completep)
         (multiple-value-call-plan build (cddr form) :literal-proofs nil)
       (declare (ignore bindings))
       (values arguments domains completep)))))

(defun asserted-sequence-expression (build source expression)
  ;; Export the already proved native shape to the host compiler. Without it
  ;; COERCE may leave an unreachable extended-sequence/MOP branch in code.
  (let ((domain (value-domain build source)))
    `(the ,(cond ((subtype-domain-p build domain 'list) 'list)
                 ((subtype-domain-p build domain 'vector) 'vector)
                 (t '(or list vector))) ,expression)))

(defun coerce-indirect-arguments (build form transformed)
  "Annotate only the actual first argument; retain call/value producer order."
  (multiple-value-bind (arguments domains completep) (ordinary-call-argument-plan build form)
    (if (not completep) transformed
        (let ((source (first arguments)) (*argument-domains* (append domains *argument-domains*)))
          (case (car form)
            (funcall (cons (asserted-sequence-expression build source (first transformed)) (cdr transformed)))
            (apply
             (cond ((cdr transformed)
                    (cons (asserted-sequence-expression build source (first transformed)) (cdr transformed)))
                   ((eq (car (car (last (cddr form)))) 'list)
                    (let ((tail (first transformed)))
                      (list (list* 'list (asserted-sequence-expression build source (second tail)) (cddr tail)))))
                   (t transformed)))
            (multiple-value-call
             (let ((firstp t))
               (mapcar (lambda (producer)
                         (if (and firstp (cdr producer))
                             (progn (setf firstp nil)
                                    (list* 'values (asserted-sequence-expression build source (second producer))
                                           (cddr producer))) producer)) transformed)))
            (otherwise transformed))))))

(defun ordinary-indirect-result-domain (build form)
  (when (member (car form) '(funcall apply multiple-value-call))
    (let ((targets (known-function-targets build (second form))))
      (when (and targets (every (lambda (target) (member target '(fill coerce))) targets))
        (multiple-value-bind (arguments domains completep) (ordinary-call-argument-plan build form)
          (when completep
            (let ((*argument-domains* (append domains *argument-domains*)))
             (values (reduce (lambda (old target)
                              (merge-value-domains build old
                                (if (eq target 'coerce) (coerce-result-domain build arguments)
                                    (value-domain build (first arguments)))))
                            targets :initial-value :pending) t))))))))

(defun audit-ordinary-operation (build name arguments local open &key variable-tail)
  "Apply one logical observation/callback policy to direct and indirect calls."
  (let ((equality-positions nil))
  (unless (member-name name local)
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
        (let ((realization (and (not open)
                                (member 'equalp (known-function-targets build reference))
                                (mapping-equality-realization build name data variable-tail))))
          (if variable-tail (validate-callback build reference arity local open)
              (validate-callback build reference arity local open :data data :equalp-realization realization))
          (when (eq realization :identity) (push 0 equality-positions)))))
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
                              (validate-keyword-callbacks build (cddr arguments) local open realization))))))
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
                                   (some (lambda (actual) (member actual (getf layout :ancestors)))
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
  (cond ((symbolp form) (resolved-function build form))
        ((and (consp form) (eq (car form) 'lambda)) form)
        ((and (consp form) (eq (car form) 'function)) (second form))
        ((and (consp form) (eq (car form) 'load-time-value)) (known-function-target build (second form)))
        (t (or (domain-function-target (value-domain build form)) :unknown))))

(defun immediate-function-reference (form)
  ;; Only this literal occurrence is consumed by the enclosing indirect call.
  ;; Other captures in a computed function expression may escape independently.
  (loop while (and (consp form) (eq (car form) 'load-time-value))
        do (setf form (cadr form)))
  (when (and (consp form) (eq (car form) 'function)) form))

(defun immediate-lambda-form (build call)
  ;; Only this literal FUNCALL occurrence establishes its binding tuple. An
  ;; escaping lambda or a separately stored/called closure gets no such fact.
  (when (eq (car call) 'funcall)
    (let ((callee (second call)))
      (when (and (consp callee) (eq (car callee) 'function)) (setf callee (second callee)))
      (when (and (consp callee) (eq (car callee) 'lambda))
        (let ((contract (lambda-contract build (second callee))))
          (unless (or (getf contract :optional) (getf contract :keyp) (getf contract :rest))
            callee))))))

(defun known-function-targets (build form)
  "Return a complete finite target set, or NIL when any alternative is unknown."
  (let ((target (known-function-target build form)))
    (if (and target (not (eq target :unknown))) (list target)
        (unless (and (symbolp form) (special-variable-p build form))
          (let ((alternatives (domain-alternatives (value-domain build form))))
            (when (every #'domain-function-target alternatives)
              (remove-duplicates (mapcar #'domain-function-target alternatives) :test #'name=)))))))

(defun function-expression-target (form)
  (when (and (consp form) (eq (car form) 'load-time-value)) (setf form (cadr form)))
  (if (and (consp form) (eq (car form) 'function)) (cadr form) :unknown))

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
       (values (cons (value-domain build initializer) (function-expression-target initializer))
               (funcall process initializer))))
   (lambda (name fact scope)
     (let ((specialp (or (assoc name specials) (special-variable-p build name))))
       (when specialp (pushnew name active-specials))
       (cons (acons name (if specialp :unknown (car fact)) (car scope))
             (acons name (if specialp :unknown (cdr fact)) (cdr scope)))))
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
                   ((incf decf) (write-to (second form) '(+ 0)) (mapc #'walk (cddr form)))
                   ((push pushnew) (write-to (third form) '(cons nil nil)) (mapc #'walk (cdr form)))
                   (pop (write-to (second form) '(cdr nil)))
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
    (find-if (lambda (fact) (and (eq name (first fact)) (eq binding (second fact))))
             *mutable-invariant-bindings*)))

(defun binding-value-domain (name)
  ;; Predicate refinement cannot restore an initial or path-local fact across
  ;; an admitted write. Only the proved broad invariant survives for this
  ;; exact binding; a shadowing binder gets an independent fact.
  (let ((mutable (mutable-binding-fact name)))
    (if mutable (third mutable) (or (cdr (assoc name *argument-domains*)) :unknown))))

(defun source-body-flow-facts (build body)
  "Invalidate assigned lexical value/callee facts before every body analysis.
NUMBER/LIST are optional precision improvements, proved jointly against all
writes under widened bindings. Failure widens to UNKNOWN, never rejects SETQ
by itself. Existing consumers still demand their own representation/call proof."
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
                 (domain (cond ((or (member name numeric) (subtype-domain-p build previous 'number)) 'number)
                               ((subtype-domain-p build previous 'list) 'list)
                               (t :unknown)))
                 (binding (assoc name functions)))
            ;; Do not mutate a captured outer alist cell. Keeping already
            ;; unknown binding-cons identity preserves enclosing invariants.
            (unless (and binding (eq (cdr binding) :unknown))
              (setf functions (acons name :unknown (remove name functions :key #'car)))
              (setf binding (assoc name functions)))
            (setf (cdr fact) domain)
            (let ((candidate (list name binding domain)))
              (push candidate candidates) (push candidate invariants))))))
    (let ((*argument-domains* domains) (*function-bindings* functions)
          (*mutable-invariant-bindings* invariants))
      ;; At most one widening per candidate. Recheck dependencies after any
      ;; loss of precision; no assignment may borrow a failed neighbor's fact.
      (loop with changed = nil do
        (setf changed nil)
        (dolist (candidate candidates)
          (when (and (not (eq (third candidate) :unknown))
                     (not (every (lambda (write)
                                   (or (not (eq (car write) (first candidate)))
                                       (subtype-domain-p build (value-domain build (cdr write))
                                                         (third candidate)))) writes)))
            (setf (third candidate) :unknown
                  (cdr (assoc (first candidate) domains)) :unknown
                  changed t)))
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

(defstruct (return-summary (:constructor make-return-summary (domains completep)))
  domains completep)

(defun return-summary-primary (summary)
  (if (return-summary-p summary)
      (if (return-summary-domains summary) (car (return-summary-domains summary)) '(eql nil))
      summary))

(defun same-return-summary-p (a b)
  (or (eq a b)
      (and (return-summary-p a) (return-summary-p b)
           (eq (return-summary-completep a) (return-summary-completep b))
           (equal (return-summary-domains a) (return-summary-domains b)))))

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
            (and old-complete-p new-complete-p (= (length old) (length new))))))))

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
        (*function-bindings* (when lexical *function-bindings*)))
    (multiple-value-bind (scope ordinary initializers)
        (analyze-lambda-scope build lambda-list domains :method method :returns #'form-return-summary
                             :specials (body-special-domains body))
      (declare (ignore ordinary))
      (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
        (reduce (lambda (old new) (merge-return-summaries build old new))
                (mapcan #'identity initializers)
                :initial-value (ordinary-return-summary build body))))))

(defun source-call-return-summary (build name)
  (when (and (build-function-returns build)
             (not (member-name name *value-domain-local-functions*)))
    (cond ((ordinary-function-form build name)
           (gethash name (build-function-returns build) :pending))
          ((member-name name (getf (build-declaration build) :closed-generics))
           (gethash name (build-function-returns build) :pending))
          ((member-name name (getf (build-declaration build) :external-operations))
           (let ((contract (assoc name (getf (build-declaration build) :external-return-domains) :test #'name=)))
             (if contract (make-return-summary (copy-tree (second contract)) t)
                 (make-return-summary (list :external-result) nil)))))))

(defun source-truth (build form)
  (let ((domain (value-domain build form)))
    (when (and (consp domain) (eq (car domain) 'eql))
      (if (null (cadr domain)) :false :true))))

(defun standard-operation-meaning-p (build name &optional local)
  (not (or (member-name name local) (member-name name *value-domain-local-functions*)
           (member-name name (build-functions build))
           (member-name name (getf (build-declaration build) :closed-generics)))))

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
       (if (and quotedp (or (member-name class (build-classes build)) (native-value-type-p class)))
           (let ((previous (binding-value-domain (second test))))
             (acons (second test) (if (subtype-domain-p build previous class) previous class) *argument-domains*))
           *argument-domains*)))
    (t *argument-domains*)))

(defmacro with-predicate-domains ((build test truep &optional local) &body body)
  `(let ((*argument-domains* (predicate-refined-domains ,build ,test ,truep ,local))) ,@body))

(defun settle-return-summary (build name)
  (let ((summary (gethash name (build-function-returns build) :pending)))
    (cond ((eq summary :pending)
           (setf (gethash name (build-function-returns build)) (make-return-summary (list :unknown) nil)
                 *function-flow-changed* t))
          ((member :pending (return-summary-domains summary))
           (setf (gethash name (build-function-returns build))
                 (make-return-summary (substitute :unknown :pending (return-summary-domains summary))
                                      (return-summary-completep summary))
                 *function-flow-changed* t)))))

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
     (let ((lambda (immediate-lambda-form build form)))
       (lambda-return-summary build (second lambda)
                              (mapcar (lambda (argument) (value-domain build argument)) (cddr form))
                              (cddr lambda) :lexical t)))
    ((and (build-function-returns build) (member (car form) '(funcall apply multiple-value-call)))
     (let ((targets (known-function-targets build (cadr form))))
       (if targets
           (reduce (lambda (old name)
                     (merge-return-summaries build old
                       (or (source-call-return-summary build name) (make-return-summary (list :unknown) nil))))
                   targets :initial-value :pending)
           (make-return-summary (list (value-domain build form)) nil))))
    ((source-call-return-summary build (car form)) (source-call-return-summary build (car form)))
    (t (make-return-summary (list (value-domain build form)) nil))))

(defun analyze-multiple-value-scope (build variables producer process &key open specials)
  (snowgrave::analyze-source-multiple-value-bindings
   variables producer (cons (copy-tree *argument-domains*) (copy-list *function-bindings*))
   (lambda (form scope)
     (let* ((*argument-domains* (car scope)) (*function-bindings* (cdr scope))
            (summary (form-return-summary build form))
            (completep (and (return-summary-p summary) (return-summary-completep summary)))
            ;; An incomplete summary still owns the ordinary primary value,
            ;; which is exactly MVB's first binding (including zero-value NIL).
            ;; Other proved positions may survive variable-count joins, with
            ;; their possible padding included; no missing tail is invented.
            (domains (when (return-summary-p summary) (return-summary-domains summary)))
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
               (funcall process form) completep)))
   (lambda (name kind fact scope)
     (let ((fact (case kind (:provided fact) (:missing (cons '(eql nil) :unknown))
                       (:unknown (cons :unknown :unknown)))))
       (cons (acons name (car fact) (car scope)) (acons name (cdr fact) (cdr scope)))))
   :source-key (build-source-key build) :path (list (build-identity build))))

(defun multiple-value-call-plan (build producers &key (literal-proofs t))
  "Describe a finite complete producer tuple without executing its proof forms.
Runtime bindings preserve each original producer; opaque domain facts feed the
existing call audits. Literal VALUES keeps its stronger source-tree proofs."
  (let (arguments bindings domains)
    (dolist (producer producers)
      (let ((summary (form-return-summary build producer)))
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

(defun indirect-argument-audit-p (build name local)
  ;; A returned cohort GF retains its source identity inside a same-name FLET.
  (or (member-name name (getf (build-declaration build) :closed-generics))
      (and (not (member-name name local))
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
                (let ((*value-domain-local-functions*
                        (append (mapcar #'car (cadr form)) *value-domain-local-functions*)))
                  (nconc
                   (mapcan (lambda (definition)
                             (multiple-value-bind (scope ordinary initializers)
                                 (analyze-lambda-scope build (cadr definition) nil :returns describe
                                                       :specials (body-special-domains (cddr definition)))
                               (declare (ignore ordinary))
                               (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
                                 (nconc (mapcan #'identity initializers) (walk-body (cddr definition)))))) (cadr form))
                   (walk-body (cddr form)))))
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
        ((simple-vector-p form) 'simple-vector)
        ((characterp form) 'character)
        ((or (keywordp form) (eq form t) (null form)) (list 'eql form))
        ((symbolp form) (if (special-variable-p build form) :unknown
                           (binding-value-domain form)))
        ((and (consp form) (member (car form) '(progn locally)))
         (body-value-domain build (cdr form)))
        ((and (consp form) (eq (car form) 'block))
         (primary-return-domain build (cddr form)))
        ((and (consp form) (member (car form) '(return-from go))) :pending)
        ((and (consp form) (eq (car form) 'tagbody)) '(eql nil))
        ((and (consp form) (eq (car form) 'the))
         (let ((input (value-domain build (third form))))
           (values (cond ((external-result-domain-p input) :external-result)
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
         (let ((*value-domain-local-functions*
                 (append (mapcar #'car (cadr form)) *value-domain-local-functions*)))
           (body-value-domain build (cddr form))))
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
               (*declared-specials* nil) (*value-domain-local-functions* nil))
           (value-domain build (second form))))
        ((and (consp form) (standard-operation-meaning-p build (car form))
              (member (car form) '(typep integerp rationalp floatp realp complexp stringp characterp
                                  vectorp arrayp symbolp consp listp endp null not keywordp numberp
                                  = /= < > <= >= eq eql equal equalp))) 'boolean)
        ((and (consp form) (standard-operation-meaning-p build (car form))
              (member (car form) '(+ - * / 1+ 1- max min abs mod rem))) 'number)
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
        ((and (consp form) (eq (car form) 'reverse))
         (let ((input (value-domain build (cadr form))))
           (values (cond ((external-result-domain-p input) :external-result)
                         ((subtype-domain-p build input 'list) 'list)
                         ((subtype-domain-p build input 'string) 'string)
                         ((subtype-domain-p build input 'vector) 'vector)
                         (t :unknown)) t)))
        ((and (consp form) (eq (car form) 'coerce)
              (standard-operation-meaning-p build 'coerce))
         (coerce-result-domain build (cdr form)))
        ((and (consp form) (eq (car form) 'fill)
              (standard-operation-meaning-p build 'fill))
         ;; FILL returns its original sequence by identity. The value and
         ;; bounds affect mutation, not the returned sequence's provenance.
         (values (value-domain build (second form)) t))
        ((and (consp form) (eq (car form) 'make-instance))
         (multiple-value-bind (class constantp) (quoted-value (cadr form))
           (if (and constantp (member-name class (build-classes build))) class :unknown)))
        ((and (consp form) (immediate-lambda-form build form))
         (return-summary-primary (form-return-summary build form)))
        ((and (consp form) (member (car form) '(funcall apply multiple-value-call)))
         (multiple-value-bind (ordinary precise-p) (ordinary-indirect-result-domain build form)
           (if precise-p (values ordinary t)
               (let ((targets (and (build-function-returns build)
                                   (known-function-targets build (cadr form)))))
                 (if targets
                     (reduce (lambda (previous name)
                               (merge-value-domains build previous
                                 (return-summary-primary (or (source-call-return-summary build name) :unknown))))
                             targets :initial-value :pending)
                     :unknown)))))
        ((and (consp form) (source-call-return-summary build (car form)))
         (return-summary-primary (source-call-return-summary build (car form))))
        (t :unknown)))

(defun subtype-domain-p (build actual expected)
  (cond ((eq expected t) t)
        ((member actual '(:unknown :pending :external-result)) nil)
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
  (every (lambda (actual) (member-name actual (build-classes build))) (domain-alternatives domain)))

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
  (cond ((eq previous :pending) additional)
        ((eq additional :pending) previous)
        ;; UNKNOWN must not erase the fact that a possible return came from
        ;; an opaque native boundary. Otherwise a join can authorize a closed
        ;; class observation of the actual original CLOS object.
        ((or (external-result-domain-p previous) (external-result-domain-p additional)) :external-result)
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

(defun call-lambda-domains (build lambda-list supplied variable-tail &key method specials)
  "Project raw caller facts through the shared lambda binding owner."
  (let* ((contract (lambda-contract build lambda-list :method method))
         (inputs (lambda-input-variables contract)))
    (let ((*argument-domains* nil) (*function-bindings* nil) (*value-domain-local-functions* nil))
      (multiple-value-bind (key-inputs unknown-key-tail)
          (call-key-inputs contract supplied variable-tail)
        (multiple-value-bind (scope ordinary initializers)
            (analyze-lambda-scope build lambda-list supplied :call-inputs t :variable-tail variable-tail
                                  :method method :key-inputs key-inputs :unknown-key-tail unknown-key-tail
                                  :specials specials)
          (declare (ignore ordinary initializers))
          (mapcar (lambda (name) (cdr (assoc name (car scope)))) inputs))))))

(defun call-function-domains (build form arguments capture variable-tail)
  "Derive effective argument bindings through the shared lambda scope owner."
  (let* ((lambda-list (caddr form))
         (inputs (lambda-input-variables (lambda-contract build lambda-list))))
    (if capture (make-list (length inputs) :initial-element :unknown)
        (call-lambda-domains build lambda-list
                             (mapcar (lambda (argument) (value-domain build argument)) arguments)
                             variable-tail :specials (body-special-domains (cdddr form))))))

(defun audit-generic-call-shape (build name arguments capture variable-tail)
  ;; Raw argument counts are input facts, not multiple-value results. Keep
  ;; omission distinct from supplied NIL, and never pad them as result tuples.
  (when (and (build-generic-call-shapes build)
             (member-name name (getf (build-declaration build) :closed-generics)))
    (let* ((contract (lambda-contract build (sb-mop:generic-function-lambda-list (open-generic build name))))
           (required (length (getf contract :required)))
           (actual (unless capture (mapcar (lambda (argument) (value-domain build argument)) arguments)))
           ;; Keep literal key names apart before joining their value domains.
           ;; Same-arity calls with different keys must not turn omission of a
           ;; method key into an unknown keyword tail. This also covers a
           ;; &REST generic whose congruent methods accept &KEY.
           (key (list (not (null capture)) (not (null variable-tail)) (length actual)
                      (mapcar (lambda (domain)
                                (when (and (consp domain) (eq (car domain) 'eql) (symbolp (second domain))) domain))
                              (nthcdr required actual))))
           (shapes (gethash name (build-generic-call-shapes build))))
      ;; Required bindings already belong to the MOP cell and the existing
      ;; generic tuple audit. No optional/key facts need caller-shape evidence
      ;; for a required-only contract, including an otherwise unreached helper.
      (unless (or (getf contract :optional) (getf contract :rest) (getf contract :keyp))
        (return-from audit-generic-call-shape nil))
      ;; Pending key names must not become a permanent unknown-name profile
      ;; when their helper return is discovered by a later iteration.
      (when (or capture (and (>= (length actual) required)
                             (not (member :pending (nthcdr required actual)))))
        (when (and *collect-function-flow* (null shapes))
          (setf shapes (make-hash-table :test #'equal)
                (gethash name (build-generic-call-shapes build)) shapes))
        (multiple-value-bind (previous presentp) (if shapes (gethash key shapes) (values nil nil))
         (cond (*collect-function-flow*
               (let ((merged (if presentp
                                 (mapcar (lambda (old new) (merge-value-domains build old new))
                                         previous actual)
                                 actual)))
                 (unless (and presentp (equal merged previous))
                   (setf (gethash key shapes) merged)
                   (setf *function-flow-changed* t))))
              ((or (not presentp)
                   (not (every (lambda (value expected)
                                 (or (eq expected :unknown) (subtype-domain-p build value expected)))
                               actual previous)))
               (fail build 'snowgrave:incomplete-domain :generic-call-bindings
                     (format nil "Caller of ~S lacks its raw argument binding proof." name) :reachability))))))))

(defun method-binding-domains (build generic lambda-list body)
  "Derive method inputs from raw generic calls; the MOP still owns dispatch.
Required bindings use the emitted cell. Nonrequired facts conservatively join
all call shapes of this generic, without a second applicability algorithm."
  (let* ((inputs (lambda-input-variables (lambda-contract build lambda-list :method t)))
         (required (length *cell-domains*))
         (summary nil) (shapes (gethash generic (build-generic-call-shapes build))))
    (when shapes
     (maphash
      (lambda (key domains)
       (destructuring-bind (capture variable-tail count literal-names) key
        (declare (ignore count literal-names))
        (let* ((supplied (append *cell-domains* (unless capture (nthcdr required domains))))
               (actual (call-lambda-domains build lambda-list supplied (or capture variable-tail)
                                           :method t :specials (body-special-domains body))))
          (setf summary (if summary
                            (mapcar (lambda (old new) (merge-value-domains build old new)) summary actual)
                            actual))))) shapes))
    (or summary (append *cell-domains*
                        (make-list (- (length inputs) required)
                                   :initial-element (if *collect-function-flow* :pending :unknown))))))

(defun audit-function-call (build name arguments &key capture variable-tail)
  (when (build-function-domains build)
    (let ((form (ordinary-function-form build name)))
      (when form
        (let* ((required (ordinary-lambda-list build (caddr form)))
               (count (length required))
               (entryp (member-name name (getf (build-declaration build) :entries)))
               (actual (call-function-domains build form arguments capture variable-tail)))
          ;; An ordinary lambda list rejects an incomplete tuple before its
          ;; body. An escaping helper capture has arbitrary future callers.
          (when (or capture (>= (length arguments) count))
            (multiple-value-bind (previous presentp) (gethash (cadr form) (build-function-domains build))
              (cond
                (*collect-function-flow*
                 (unless (or entryp (member :pending (subseq actual 0 count)))
                   (let ((merged (if presentp
                                     (mapcar (lambda (old new) (merge-value-domains build old new)) previous actual)
                                     actual)))
                     (unless (and presentp (equal merged previous))
                       (setf (gethash (cadr form) (build-function-domains build)) merged
                             *function-flow-changed* t)))))
                ;; Captures of declared entries retain their entry guard.
                ((and capture entryp) nil)
                ((not presentp)
                 (fail build 'snowgrave:incomplete-domain :ordinary-function-reachability
                       (format nil "No caller-domain proof reaches ordinary helper ~S." name) :reachability))
                ((and capture (not (every (lambda (domain) (eq domain :unknown)) previous)))
                 (fail build 'snowgrave:incomplete-domain :ordinary-function-capture-domain
                       (format nil "Escaping helper ~S lacks an arbitrary-caller proof." name) :reachability))
                ((and (not capture)
                      (not (every (lambda (value expected)
                                    (or (eq expected :unknown) (subtype-domain-p build value expected)))
                                  actual previous)))
                 (fail build 'snowgrave:incomplete-domain :ordinary-function-call-domain
                       (format nil "Caller of ~S supplies ~S outside proved required domains ~S." name actual previous)
                       :reachability))))))))))

(defun audit-function-capture (build name)
  (when (member name '(fill coerce))
    (fail build 'snowgrave:unclosed-call :ordinary-function-capture
          "This ordinary operator needs a proved callable ABI before its unchecked host function can escape; use an audited immediate call."))
  (audit-generic-call-shape build name nil t nil)
  (audit-function-call build name nil :capture t))

(defun audit-place-writer (build place value local)
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
  (audit-generic-call-shape build name arguments nil variable-tail)
  (when (member-name name (getf (build-declaration build) :closed-generics))
    (when (and (not *collect-function-flow*)
               (some (lambda (argument) (external-result-domain-p (value-domain build argument))) arguments))
      (fail build 'snowgrave:unclosed-call :external-result-dispatch
            "Closed dispatch needs an admitted representation for values returned by an external operation." :reachability))
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

(defun transform-body (build body package &key open next original local)
  (with-source-body-facts (body)
   (let ((*value-domain-local-functions* local))
    (multiple-value-bind (prefix executable) (snowgrave::source-body-parts body)
      (append (mapcar (lambda (form)
                        ;; Documentation is syntax, not a literal expression.
                        (if (stringp form) form
                            (transform-form build form package :open open :next next
                                            :original original :local local))) prefix)
              (mapcar (lambda (form)
                        (transform-form build form package :open open :next next
                                        :original original :local local)) executable))))))

(defun declared-external-result-expression (build name expression)
  (let ((contract (assoc name (getf (build-declaration build) :external-return-domains) :test #'name=)))
    (if (and contract (not *collect-function-flow*))
        `(the (values ,@(mapcar (lambda (domain) (external-result-native-type build domain)) (second contract)) &optional)
           ,expression) expression)))

(defun transform-form (build form package &key open next original local)
  (labels
      ((walk (x) (transform-form build x package :open open :next next
                                :original original :local local))
       (body (xs) (transform-body build xs package :open open :next next :original original :local local))
       (target (name)
         (transformed-function-name build name package open local))
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
       (if (or (stringp form) (simple-vector-p form))
           (literal-reference build form package) form))
      ((eq (car form) 'quote)
       (unless (serializable-tree-p (cadr form))
         (fail build 'snowgrave:residual-metaobject :quoted-object
               "Only ordinary readable scalar/list constants are admitted."))
       (if (or (consp (cadr form)) (stringp (cadr form)) (simple-vector-p (cadr form)))
           (literal-reference build (cadr form) package) form))
      ((eq (car form) 'function)
       (if (and (consp (cadr form)) (eq (caadr form) 'lambda))
           `(function ,(walk (cadr form)))
           (progn
             (unless (or (member-name (cadr form) local)
                         (eq form *immediate-function-reference*))
               (audit-function-capture build (cadr form)))
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
       form)
      ((eq (car form) 'call-next-method)
       (cond (open form)
             ((cdr form)
              (fail build 'snowgrave:unsupported-definition :changed-argument-next-method
                    "Changed-argument next methods need the host's exact continuation/error mapping."))
             (next `(,next ,@original))
             (*current-method*
              (emit-standard-miss build 'no-next-method
                                  (first *current-method*) (second *current-method*)
                                  (if *fixed-effective-arguments* `(list ,@original) (car original))))
             (t (fail build 'snowgrave:mop-failure :no-next-method-context
                      "CALL-NEXT-METHOD has no reproducible authored method context." :materialization))))
      ((eq (car form) 'next-method-p) (if open form (not (null next))))
      ((eq (car form) 'if)
       (let ((test (walk (cadr form))))
         (cond ((eq test t) (with-predicate-domains (build (second form) t local) (walk (third form))))
               ((null test) (with-predicate-domains (build (second form) nil local) (walk (fourth form))))
               (t `(if ,test
                       ,(with-predicate-domains (build (second form) t local) (walk (third form)))
                       ,(with-predicate-domains (build (second form) nil local) (walk (fourth form))))))))
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
       (let* ((definitions (cadr form))
              (names (mapcar #'car definitions))
              (inner (append names local)))
         `(,(car form)
           ,(mapcar (lambda (definition)
                      (multiple-value-bind (scope ordinary)
                          (analyze-lambda-scope build (cadr definition) nil :package package :open open
                                               :local (if (eq (car form) 'labels) inner local)
                                               :next next :original original
                                               :specials (body-special-domains (cddr definition)))
                       (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
                        (list* (car definition) ordinary
                               (append (when (source-specials build)
                                         (list `(declare (special ,@(source-specials build)))))
                                       (transform-body build (cddr definition) package
                                               :open open :next next :original original
                                               :local (if (eq (car form) 'labels) inner local)))))))
                    definitions)
           ,@(transform-body build (cddr form) package :open open :next next
                             :original original :local inner))))
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
       `(the ,(second form) ,(walk (third form))))
      ((member (car form) '(block return-from catch throw))
       `(,(car form) ,(if (member (car form) '(catch throw))
                         (walk (cadr form)) (cadr form))
         ,@(body (cddr form))))
      ((member (car form) '(and or))
       (labels ((terms (arguments)
                  (when arguments
                    (cons (walk (car arguments))
                          (with-predicate-domains (build (car arguments) (eq (car form) 'and) local)
                            (terms (cdr arguments)))))))
         `(,(car form) ,@(terms (cdr form)))))
      ((member (car form) '(when unless))
       `(,(car form) ,(walk (second form))
          ,@(with-predicate-domains (build (second form) (eq (car form) 'when) local) (body (cddr form)))))
      ((member (car form) '(progn locally unwind-protect multiple-value-prog1))
       `(,(car form) ,@(body (cdr form))))
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
      ((eq (car form) 'load-time-value)
       (unless (reproducible-global-p build (cadr form))
         (fail build 'snowgrave:nonreproducible-source :load-time-capture
               "LOAD-TIME-VALUE must have a reproducible checked constant/function initializer."))
       `(load-time-value
          ,(let ((*argument-domains* nil) (*function-bindings* nil)
                 (*declared-specials* nil) (*value-domain-local-functions* nil)
                 (*mutable-invariant-bindings* nil) (*tagbody-targets* nil)
                 (*current-method* nil))
             (transform-form build (cadr form) package :open open))
          ,@(cddr form)))
      ((member (car form) '(funcall apply multiple-value-call))
       (when (special-variable-p build (cadr form))
         (fail build 'snowgrave:unclosed-call :mutable-function-special
               "A callable special needs a sealed binding-domain proof; use a lexical or direct LOAD-TIME-VALUE capture in this fragment."))
       (unless (or open *collect-function-flow*
                   (and (consp (cadr form))
                        (or (member (caadr form) '(function lambda))
                            (and (eq (caadr form) 'load-time-value)
                                 (not (eq (function-expression-target (cadr form)) :unknown)))))
                   (known-function-targets build (cadr form)))
         (fail build 'snowgrave:unclosed-call :computed-function
               "Indirect calls require a checked FUNCTION/LAMBDA, immutable capture, or a complete finite set of named source targets."))
       (let ((equality-realization nil) (mapping-plans nil)
             (value-arguments nil) (value-bindings nil) (value-count-complete-p t)
             (*argument-domains* *argument-domains*))
       (when (and (not open) (eq (car form) 'multiple-value-call)
                  (not (every (lambda (producer) (and (consp producer) (eq (car producer) 'values))) (cddr form)))
                  (some (lambda (name) (indirect-argument-audit-p build name local))
                        (known-function-targets build (cadr form))))
         (multiple-value-bind (arguments bindings domains completep)
             (multiple-value-call-plan build (cddr form))
           (setf value-arguments arguments value-bindings bindings value-count-complete-p completep
                 *argument-domains* (append domains *argument-domains*))
           (unless (or completep *collect-function-flow*)
             (fail build 'snowgrave:incomplete-domain :multiple-value-arguments
                   "A multiple-value producer needs an exact ordered value-count/domain contract." :reachability))))
       (unless open
         (dolist (name (known-function-targets build (cadr form)))
          (let ((arguments (cddr form)) (variable-tail nil))
           ;; A returned global GF retains its source identity even inside a
           ;; same-named FLET. Local-name membership cannot waive its tuple.
           (when (and value-count-complete-p (indirect-argument-audit-p build name local))
             (when (eq (car form) 'apply)
               (let ((last (car (last arguments)))
                     (prefix (butlast arguments))
                     (required (if (ordinary-function-form build name)
                                   (length (ordinary-lambda-list build (caddr (ordinary-function-form build name))))
                                   (if (or (member name '(eq eql equal equalp))
                                           (member name *representation-sensitive-ordinary-operations*)
                                           (member-name name (getf (build-declaration build) :external-operations)))
                                       (length (ordinary-lambda-list build (sb-introspect:function-lambda-list (fdefinition name))))
                                       (length (generic-domain-roots build name))))))
                 (cond ((and (consp last) (eq (car last) 'list))
                        (setf arguments (append (butlast arguments) (cdr last))))
                       ((and (consp last) (eq (car last) 'quote) (listp (cadr last)))
                        (setf arguments (append (butlast arguments)
                                                (mapcar (lambda (x) (list 'quote x)) (cadr last)))))
                       ((>= (length prefix) required)
                        (when (and (initialization-generic-p name) (not *generated-class-operation*))
                          (fail build 'snowgrave:unclosed-class-operation :initialization-apply-tail
                                "A variable initialization APPLY tail needs a proven keyword/error shape." :reachability))
                        (setf arguments prefix variable-tail t))
                       (t (fail build 'snowgrave:incomplete-domain :apply-arguments
                                "A variable APPLY tail cannot prove that every execution supplies the required tuple." :reachability)))))
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
                     (record-equality-realization build arguments :variable-tail variable-tail)))))))
       (let ((coerce-p (and (not open) (not *collect-function-flow*)
                             (equal (known-function-targets build (cadr form)) '(coerce))))
             (callee (let ((*immediate-function-reference*
                            (immediate-function-reference (cadr form)))
                           (*immediate-lambda-domains*
                             (let ((lambda (immediate-lambda-form build form)))
                               (if lambda
                                   (acons lambda
                                          (mapcar (lambda (argument) (value-domain build argument)) (cddr form))
                                          *immediate-lambda-domains*)
                                   *immediate-lambda-domains*))))
                       (walk (cadr form)))))
         (cond (value-bindings
                (let* ((binding (gensym "VALUE-CALLEE"))
                       (arguments (mapcan (lambda (producer) (copy-list (first producer))) value-bindings))
                       (invocation
                         `(funcall ,(if (eq equality-realization :identity)
                                        `(if (eq ,binding #'equalp) #'eq ,binding) binding)
                                   ,@(cond (coerce-p
                                            (cons (asserted-sequence-expression build (first value-arguments) (first arguments))
                                                  (cdr arguments)))
                                           (mapping-plans (equality-arguments arguments mapping-plans binding))
                                           (t arguments)))))
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
                   ,@(if mapping-plans (call-equality-arguments form binding mapping-plans)
                         (body (cddr form)))))))
               (t (let ((expression `(,(car form) ,callee
                                         ,@(let ((arguments (body (cddr form))))
                                             (if coerce-p (coerce-indirect-arguments build form arguments) arguments))))
                        (targets (known-function-targets build (cadr form))))
                    (if (and (not open) (= (length targets) 1))
                        (declared-external-result-expression build (first targets) expression) expression)))))))
      ((member (car form) '(setq setf incf decf push pushnew pop))
       (when (eq (car form) 'pushnew) (validate-keyword-callbacks build (cdddr form) local open))
       (unless open
         (let ((places (if (member (car form) '(setq setf))
                           (loop for tail on (cdr form) by #'cddr collect (car tail))
                           (if (member (car form) '(push pushnew)) (list (caddr form)) (list (cadr form))))))
           (audit-assignment-targets build places)))
       (when (and (not open) (member (car form) '(setq setf)))
         (loop for (place value) on (cdr form) by #'cddr
               do (audit-external-place-value build place value)))
       (when (and (not open) (member (car form) '(push pushnew)))
         (audit-external-place-value build (caddr form) (cadr form)))
       (when (and (not open) (member (car form) '(incf decf push pushnew pop)))
         ;; These forms still execute as the ordinary host macros. Successful
         ;; arithmetic updates supply a number; PUSH supplies a cons. POP's
         ;; new CDR can be any object, so it contributes an unknown value.
         (audit-place-writer build (if (member (car form) '(push pushnew)) (caddr form) (cadr form))
                             (case (car form)
                               ((incf decf) '(+ 0))
                               ((push pushnew) '(cons nil nil))
                               (pop '(cdr nil))) local))
       (case (car form)
         (setf
          `(setf ,@(loop for (place value) on (cdr form) by #'cddr
                        append (progn
                                 (unless open (audit-missing-slot-writer build place value))
                                 (unless open (audit-place-writer build place value local))
                                 (list (transform-place build place package open local) (walk value))))))
         ((incf decf pop)
          `(,(car form) ,(transform-place build (cadr form) package open local :readp t)
                        ,@(body (cddr form))))
         ((push pushnew)
          `(,(car form) ,(walk (cadr form))
                        ,(transform-place build (caddr form) package open local :readp t)
                        ,@(body (cdddr form))))
         (otherwise `(,(car form) ,@(body (cdr form))))))
      ((member (car form) '(slot-value slot-boundp slot-makunbound))
       (multiple-value-bind (slot constantp) (quoted-value (caddr form))
         (unless constantp
           (fail build 'snowgrave:unclosed-class-operation :dynamic-slot
                 "A dynamic slot name needs a finite success/error dispatcher."))
         (unless open (validate-record-slot build (cadr form) slot))
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
                     (and (symbolp type) (or (member type '(t function compiled-function))
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
       (multiple-value-bind (class constantp) (quoted-value (cadr form))
         (unless (and constantp (member-name class (build-classes build)))
           (fail build 'snowgrave:unclosed-class-operation :dynamic-construction-class
                 "A construction site must name one sealed class."))
         (unless (and (evenp (length (cddr form)))
                      (loop for tail on (cddr form) by #'cddr always (keywordp (car tail))))
           (fail build 'snowgrave:unclosed-class-operation :construction-initargs
                 "Constructor sites need literal keyword names with a proven argument shape."))
         (when (and (not open) (not *collect-function-flow*)
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
       (fail build 'snowgrave:unclosed-class-operation (car form)
             "This class operation requires construction/reflection/error protocol lowering."))
      ((symbolp (car form))
       (unless (or open (member-name (car form) local))
         (audit-external-identity build (car form) (cdr form)))
       (let ((mapping-realization (audit-ordinary-operation build (car form) (cdr form) local open)))
         (when (and (not open) (not *collect-function-flow*) (eq (car form) 'equalp) (build-classes build))
           (when (eq :identity (record-equality-realization build (cdr form)))
             (return-from transform-form `(eq ,@(body (cdr form))))))
         (unless (or open (member-name (car form) local))
           (audit-generic-call build (car form) (cdr form))
           (audit-function-call build (car form) (cdr form))
           (audit-external-call build (car form) (cdr form)))
         (cond
           ((and (eq (car form) 'coerce) (not open) (not *collect-function-flow*)
                 (standard-operation-meaning-p build 'coerce local))
            `(coerce ,(asserted-sequence-expression build (second form) (walk (second form)))
                     ,(walk (third form))))
           (mapping-realization
             `(,(target (car form))
                ,@(equality-arguments (cdr form)
                                     (mapcar (lambda (position) (list position (car form))) mapping-realization))))
           (t (multiple-value-bind (callee fixedp)
                 (direct-call-name build (car form) package open local (length (cdr form)))
               (let ((expression `(,callee ,@(body (cdr form)) ,@(when fixedp '(nil)))))
                 (if (or open (member-name (car form) local)) expression
                     (declared-external-result-expression build (car form) expression))))))))
      (t (fail build 'snowgrave:unsupported-definition :computed-operator
               "Computed operator forms are not in the audited source fragment.")))))

(defun transform-place (build place package open local &key readp)
  (cond ((symbolp place)
         (if (member place (build-globals build)) (global-binding-name build place package open) place))
        ((and (consp place) (eq (car place) 'slot-value))
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
         (when (and readp (not open) (not (member-name (car place) local)))
           (audit-generic-call build (car place) (cdr place))
           (audit-function-call build (car place) (cdr place))
           (audit-external-call build (car place) (cdr place)))
         (multiple-value-bind (callee fixedp)
             (direct-call-name build (list 'setf (car place)) package open local (length place))
           ;; Read/modify/write needs BOTH conventions to agree. An unrelated
           ;; rest/key writer must never be redirected merely because its
           ;; reader has a fixed contract (or the converse).
           (when (and fixedp readp
                      (let ((arity (fixed-generic-arity build (car place))))
                        (not (and arity (= arity (length (cdr place)))))))
             (setf fixedp nil
                   callee (transformed-function-name build (list 'setf (car place)) package open local)))
           (cons (second callee)
                 (append (transform-body build (cdr place) package :open open :local local)
                         (when fixedp '(nil))))))
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
  (append (lambda-positional-variables contract) (lambda-key-variables contract)))

(defun call-key-inputs (contract supplied variable-tail)
  "Project known first-occurrence keyword inputs from already summarized facts.
The ordinary emitted lambda list still owns parsing, errors and default effects.
An unknown name makes that name and the remainder uncertain, never absent."
  (let ((tail (nthcdr (min (length supplied) (length (lambda-positional-variables contract))) supplied))
        (inputs nil))
    (loop while (cdr tail) do
      (let ((name-domain (car tail)))
        (unless (and (consp name-domain) (eq (car name-domain) 'eql) (symbolp (second name-domain)))
          (return-from call-key-inputs (values inputs t)))
        (unless (assoc (second name-domain) inputs)
          (push (cons (second name-domain) (second tail)) inputs)))
      (setf tail (cddr tail)))
    (values inputs (or variable-tail (not (null tail))))))

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
            (values (cons (value-domain build initializer) (function-expression-target initializer))
                    (cond (call-inputs nil)
                          (returns (source-return-domains build (list initializer) (if (eq returns t) #'value-domain returns)))
                          (t
                           ;; Lambda defaults run in the method's lexical next
                           ;; context, including nested local/lambda defaults.
                           ;; ORIGINAL remains the raw generic argument list;
                           ;; the current method's defaults must not replace it.
                           (transform-form build initializer package :open open :local local :next next :original original))))))
        (lambda (name kind fact scope)
          (let* ((specialp (or (assoc name specials) (special-variable-p build name)))
                 (input-domain (case kind
                               ((:required :optional)
                                (let ((index (position name positional)))
                                  (if (and call-inputs (eq kind :optional) (>= index (length binding-domains)))
                                      (if variable-tail :unknown (car fact))
                                      (or (nth index binding-domains) :unknown))))
                               (:key
                                (if call-inputs
                                    (let* ((spec (nth (position name (lambda-key-variables contract)) (getf contract :keys)))
                                           (provided (assoc (keyword-name spec) key-inputs)))
                                      (cond (provided (cdr provided)) (unknown-key-tail :unknown) (t (car fact))))
                                    (or (nth (position name inputs) binding-domains) :unknown)))
                               (:rest 'list) (:supplied-p 'boolean) (:aux (car fact)) (t :unknown)))
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

(defun open-definition (build form)
  (setf (build-source-key build) (authored-source-key build form))
  (let ((package (build-open-package build)))
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
       ;; Definition and registration remain in the host's method-combination
       ;; machinery, under an isolated name with exact authored provenance.
       `(cl:define-method-combination ,(mapped-name (cadr form) package) ,@(cddr form)))
      (:generic `(cl:defgeneric ,(mapped-name (cadr form) package) ,(third form)
                    ,@(mapcar (lambda (option) (open-generic-option build option package))
                              (cdddr form))))
      (:method
       (multiple-value-bind (qualifiers lambda-list body) (method-parts form)
        (let ((*argument-domains* nil) (*function-bindings* nil))
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
       (let ((*argument-domains* nil) (*function-bindings* nil))
        (multiple-value-bind (scope ordinary)
            (analyze-lambda-scope build (caddr form) nil :package package :open t
                                 :specials (body-special-domains (cdddr form)))
         (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
         `(defun ,(mapped-name (cadr form) package)
            ,ordinary
            ,@(preserve-source-block (cadr form) (transform-body build (cdddr form) package :open t)))))))
      (:global
       (unless (or (= (length form) 2) (reproducible-global-p build (caddr form)))
         (fail build 'snowgrave:nonreproducible-source :global-initializer
               "Global initializers admit only constants, checked captures, and pure constant construction."))
       `(,(car form) ,(global-binding-name build (cadr form) package t)
         ,@(when (> (length form) 2)
             (cons (transform-form build (caddr form) package :open t) (cdddr form))))))))

(defun reproducible-global-p (build form)
  (cond ((atom form) (or (numberp form) (stringp form) (characterp form)
                        (keywordp form) (eq form t) (null form)))
        ((eq (car form) 'quote) (serializable-tree-p (cadr form)))
        ((eq (car form) 'function) (function-target-p build (cadr form) nil))
        ((eq (car form) 'load-time-value) (reproducible-global-p build (cadr form)))
        ((member (car form) *reproducible-global-operations*)
         (every (lambda (x) (reproducible-global-p build x)) (cdr form)))
        (t nil)))

(defun staged-special-form (form specials)
  (if (member (cadr form) specials)
   (case (car form)
    (defparameter `(setf (symbol-value ',(cadr form)) ,(caddr form)))
    (defvar (if (> (length form) 2)
                `(unless (boundp ',(cadr form)) (setf (symbol-value ',(cadr form)) ,(caddr form)))
                '(values)))
    (t form)) form))

(defun literal-reference (build value package)
  ;; EQ is the source graph's authority, not structural equality. Separate
  ;; pools keep the disposable CLOS pass and the installed unit independent.
  (unless (serializable-tree-p value (build-literal-states build))
    (fail build 'snowgrave:residual-metaobject :literal-object
          "Literal graphs must contain only acyclic readable native data."))
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
    `(the ,(type-of value) (load-time-value (svref ,(literal-pool-name pool) ,index) t))))

(defun literal-pool-definition (build package)
  (let ((pool (cdr (assoc package (build-literal-pools build)))))
    (when pool
      (let ((seen (make-hash-table :test #'eq)) (bindings nil))
        (labels ((construct (value)
                   (if (or (consp value) (stringp value) (simple-vector-p value))
                       (or (gethash value seen)
                           (let* ((name (gensym "LITERAL"))
                                  (initializer
                                    (cond ((consp value) `(cons ,(construct (car value)) ,(construct (cdr value))))
                                          ((stringp value) `(copy-seq ,value))
                                          (t `(vector ,@(map 'list #'construct value))))))
                             (setf (gethash value seen) name)
                             (push (list name initializer) bindings)
                             name))
                       `',value)))
          (let ((roots (map 'list #'construct (literal-pool-values pool))))
            ;; Allocate once at load time. Only scalar leaves reach the FASL
            ;; constant dumper, so it cannot merge distinct mutable nodes.
            `(defparameter ,(literal-pool-name pool)
               (let* ,(nreverse bindings) (vector ,@roots)))))))))

(defun with-literal-pool (build forms package)
  (let ((definition (literal-pool-definition build package)))
    (if definition (cons definition forms) forms)))

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
  (unless (and candidates (every (lambda (candidate) (eq candidate (car candidates))) candidates))
    (fail build 'snowgrave:nonreproducible-source feature
          "The actual finalized initializer lacks unambiguous authored constant provenance." :materialization))
  (car candidates))

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
                    (push (getf (cdr source) :initform)
                          (gethash (list (sb-mop:slot-definition-name direct)
                                         (sb-mop:slot-definition-initfunction direct)) slots)))))))
          (let ((source-defaults (make-hash-table :test #'eq)))
            (loop for (key value) on (cdr (assoc :default-initargs (cddddr form))) by #'cddr
                  do (setf (gethash key source-defaults) (list value)))
          (dolist (direct (sb-mop:class-direct-default-initargs ancestor))
              (let ((source (gethash (car direct) source-defaults)))
                (when source
                  (push (car source) (gethash (list (car direct) (third direct)) defaults)))))))))
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
                                               (list :form (unique-authored-initializer build
                                                 (gethash (list (sb-mop:slot-definition-name slot)
                                                                (sb-mop:slot-definition-initfunction slot)) slot-provenance)
                                                 :slot-initform-provenance)))) slots)
                    :default-initargs (mapcar (lambda (default)
                                               (list (car default) (unique-authored-initializer build
                                                 (gethash (list (car default) (third default)) default-provenance)
                                                 :default-initform-provenance)))
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
                                     ,(transform-form build (getf initform :form) (build-output-package build)) '(,class))))))))
                  (getf description :slots) (getf description :slot-initargs) (getf description :slot-initforms))
               ,record))
          (build-generated build))
    `(,name ,@parameters)))

(defun emit-initialization-generic (build generic)
  (let* ((*fixed-effective-arguments* nil)
         (gf (fdefinition generic))
         (record (fresh-name build "RECORD"))
         (slots (when (eq generic 'shared-initialize) (fresh-name build "SLOT-NAMES")))
         (tail (fresh-name build "INITARGS"))
         (arguments (fresh-name build "ARGUMENTS"))
         (clauses nil) (descriptions nil))
    (unless (and (eq (class-of gf) (find-class 'standard-generic-function))
                 (typep (sb-mop:generic-function-method-combination gf) 'sb-pcl::standard-method-combination))
      (fail build 'snowgrave:unclosed-class-operation :initialization-generic-protocol
            "Initialization generic classes and combinations require exact host normalization." :materialization))
    (dolist (layout (build-layouts build))
      (let* ((class (getf layout :class))
             (host-class (find-class (mapped-name class (build-open-package build))))
             (methods (initialization-methods build generic host-class))
             (*cell-domains* (append (list class) (when slots (list t)))))
        (multiple-value-bind (effective options)
            (sb-mop:compute-effective-method gf (sb-mop:generic-function-method-combination gf) methods)
          (when options (fail build 'snowgrave:unsupported-definition :effective-method-options
                              "Initialization MOP options require normalization." :materialization))
          (let ((validator (emit-argument-validator build generic gf methods)))
            (push `(,(record-layout-test build class record)
                     (apply #',validator ,arguments)
                     ,(emit-effective build generic effective (list arguments))) clauses)))
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
                   (snowgrave:make-reference-domain ',(build-identity build) ',(build-layouts build)))
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
             (*argument-domains* nil))
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
        (push (cons class name) (build-constructors build))
        (push `(defun ,name (&rest ,arguments)
                 (let ((,defaults nil))
                   ,@(mapcar
                      (lambda (default)
                        `(unless (nth-value 2 (get-properties ,arguments '(,(car default))))
                           (setf ,defaults (append ,defaults
                                                  (list ,(car default)
                                                        ,(transform-form build (cadr default) (build-output-package build)))))))
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
                                             ,(transform-form build (getf initform :form) (build-output-package build)) '(,class))))))))
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
                       (,(if *fixed-effective-arguments* 'funcall 'apply) (lambda ,ordinary
                                ,@(when (source-specials build) (list `(declare (special ,@(source-specials build)))))
                                ,@(loop while (and body (consp (car body)) (eq (caar body) 'declare))
                                        collect (transform-form build (pop body) (build-output-package build)))
                                (block ,block-name
                                  ,@(transform-body build body (build-output-package build)
                                                    :next next-name :original parameters)))
                              ,@(if *fixed-effective-arguments* parameters (list (car parameters)))))
                    (build-generated build))))))))
    (values `(,name ,@parameters) (if (eq summary :pending) '(error) summary))))))

(defun emit-effective (build generic form parameters)
  "Co-produce ordinary CEM code and a cold return proof over those same nodes.
CALL-METHOD proof leaves reuse method summaries; standard PROGN/MV-PROG1
structure is described by the existing source return composer. Nothing in
the second value enters generated code or recomputes method order."
  (cond
    ((atom form)
     (if (serializable-tree-p form) (values form form)
         (fail build 'snowgrave:residual-metaobject :effective-method-constant
               "The MOP effective method contains a builder constant." :materialization)))
    ((eq (car form) 'sb-pcl::call-method-list)
     ;; The host expands this helper to calls in their given order. Preserve
     ;; that order in ordinary PROGN; never deploy the MOP helper macro.
     (let (code proof)
       (dolist (part (cdr form))
         (multiple-value-bind (emitted description) (emit-effective build generic part parameters)
           (push emitted code) (push description proof)))
       (values `(progn ,@(nreverse code)) `(progn ,@(nreverse proof)))))
    ((eq (car form) 'call-method)
     (let ((method (cadr form)))
       (if (and (consp method) (eq (car method) 'make-method))
           (emit-effective build generic (cadr method) parameters)
           (emit-method-call build generic method (caddr form) parameters))))
    ((eq (car form) 'quote)
     (unless (serializable-tree-p (cadr form))
       (fail build 'snowgrave:residual-metaobject :effective-method-quote
             "MOP error or combination constant retains a builder metaobject." :materialization))
     (values form form))
    (t
     (let (code proof)
       (dolist (part form)
         (multiple-value-bind (emitted description) (emit-effective build generic part parameters)
           (push emitted code) (push description proof)))
       (values (nreverse code) (nreverse proof))))))

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

(defun emit-argument-validator (build generic gf applicable)
  (let* ((contract (lambda-contract build (sb-mop:generic-function-lambda-list gf)))
         (name (fresh-name build "CONTRACT"))
         (required (mapcar (lambda (x) (declare (ignore x)) (fresh-name build "CHECK-ARG")) (getf contract :required)))
         (optional (mapcar (lambda (x) (declare (ignore x)) (fresh-name build "CHECK-OPT")) (getf contract :optional)))
         (rest (when (or (getf contract :rest) (getf contract :keyp)) (fresh-name build "CHECK-REST")))
         (keywords (mapcar #'keyword-name (getf contract :keys)))
         (allow (getf contract :allow)))
    (when (getf contract :keyp)
      (dolist (method applicable)
        (let ((method-contract (lambda-contract build (sb-mop:method-lambda-list method))))
          (dolist (key (getf method-contract :keys)) (pushnew (keyword-name key) keywords))
          (when (getf method-contract :allow) (setf allow t)))))
    (let* ((key-specs (when (getf contract :keyp)
                        (mapcar (lambda (key) (list (list key (fresh-name build "CHECK-KEY")))) keywords)))
           (all-variables (append required optional (when rest (list rest))
                                  (mapcar (lambda (spec) (cadar spec)) key-specs)))
           (lambda-list (append required (when optional (cons '&optional optional))
                                (when rest (list '&rest rest))
                                (when (getf contract :keyp) (cons '&key key-specs))
                                (when (and (getf contract :keyp) allow) '(&allow-other-keys)))))
      (push `(defun ,name ,lambda-list
               ,@(when all-variables (list `(declare (ignore ,@all-variables))))
               (values)) (build-generated build))
      (values name (list :generic generic :keywords keywords :allow-other-keys allow
                         :lambda-list lambda-list)))))

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
         (fixed-arity (fixed-generic-arity build generic))
         (error-arguments (if fixed-arity `(or ,arguments (list ,@parameters)) arguments))
         (established (fresh-name build "DISPATCH-ESTABLISHED"))
         (methods (sb-mop:generic-function-methods gf))
         ;; Required-only validators are identical for every method set. Keep
         ;; one ordinary lambda contract, rather than a copy in every cell.
         (fixed-validator (when fixed-arity
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
    (unless (eq (class-of gf) (find-class 'standard-generic-function))
      (fail build 'snowgrave:unsupported-definition :generic-function-class
            "Custom generic-function classes need an exact argument/applicability/error contract." :materialization))
    (unless (or (typep (sb-mop:generic-function-method-combination gf) 'sb-pcl::standard-method-combination)
                (let ((name (source-generic-combination build generic)))
                  (or (authored-combination-name build name)
                      (member name *host-method-combinations*))))
      (fail build 'snowgrave:unsupported-definition :custom-method-combination
            "Custom combinations need their own audited normalized source extension." :materialization))
    (dolist (cell cells)
      (let ((*cell-domains* (mapcar (lambda (class) (source-class build class)) cell)))
       (multiple-value-bind (applicable certainp)
          (sb-mop:compute-applicable-methods-using-classes gf cell)
        (unless certainp
          (fail build 'snowgrave:mop-failure :applicability
                "The host cannot prove class-only applicability for this cell." :partition))
        (unless (gethash applicable verified-lists)
          (incf uniformity-replays
                (verify-universal-axes build gf cell applicable axis-evidence concrete-axes))
          (setf (gethash applicable verified-lists) t))
        (if (null applicable)
            (progn
              (when (and fixed-arity (null fixed-miss))
                (setf fixed-miss (fresh-name build "STANDARD-MISS"))
                (push fixed-miss (build-method-names build))
                (push `(defun ,fixed-miss (,arguments)
                         ,(emit-standard-miss build 'no-applicable-method generic nil arguments))
                      (build-generated build)))
              (let* ((contract (lambda-contract build lambda-list))
                     (validator (if fixed-arity (first fixed-validator)
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
          (multiple-value-bind (validator argument-contract)
              (if fixed-arity (values-list fixed-validator)
                  (emit-argument-validator build generic gf applicable))
          (multiple-value-bind (code proof)
              (let ((*fixed-effective-arguments* (not (null fixed-arity))))
                (emit-effective build generic effective (if fixed-arity parameters (list arguments))))
            (let ((*effective-return-proof* t))
              (setf summary (merge-return-summaries build summary (form-return-summary build proof))))
            (push `(,(cons 'and (mapcar (lambda (class parameter) (cell-test build class parameter))
                                       cell parameters))
                     (progn (setf ,established t)
                            ,(if fixed-arity `(when ,arguments (apply #',validator ,arguments))
                                 `(apply #',validator ,arguments))
                            ,code)) clauses))
          (push (list :classes (mapcar (lambda (class) (source-class build class)) cell)
                      :argument-contract argument-contract
                      :methods (mapcar (lambda (method)
                                         (list (source-method-qualifiers build generic method)
                                               (mapcar (lambda (specializer) (source-class build specializer))
                                                       (sb-mop:method-specializers method)))) applicable))
                descriptions)))))))
    (when *collect-function-flow*
      (let* ((previous (gethash generic (build-function-returns build) :pending))
             (merged (merge-return-summaries build previous summary)))
        (unless (same-return-summary-p previous merged)
          (setf (gethash generic (build-function-returns build)) merged
                *function-flow-changed* t))))
    (when fixed-arity
      (push `(defun ,(fixed-generic-name build generic)
                 (,@parameters ,arguments)
               (declare (special ,established))
               (cond ,@(reverse clauses)
                     (t (snowgrave:sg-domain-violation ',(build-identity build) ',generic ,error-arguments))))
            (build-generated build)))
    (push `(defun ,(mapped-name generic (build-output-package build)) (&rest ,arguments)
             (declare (special ,established))
             ,@(when parameters (list (emit-minimum-arity-check build generic gf (length parameters) established arguments)))
             (let ,(loop for parameter in parameters for position from 0
                         collect `(,parameter (nth ,position ,arguments)))
               ,(if fixed-arity `(funcall #',(fixed-generic-name build generic) ,@parameters ,arguments)
                    `(cond ,@(reverse clauses)
                           (t (snowgrave:sg-domain-violation ',(build-identity build) ',generic ,arguments))))))
          (build-generated build))
    (list :generic generic :lambda-list lambda-list
          :fixed-call-kernel (when fixed-arity (snowgrave::function-name-key (fixed-generic-name build generic)))
          :argument-precedence-order (sb-mop:generic-function-argument-precedence-order gf)
          :axis-uniformity axis-evidence
          :uniformity-replays uniformity-replays
          :cells (nreverse descriptions))))

(defun domain-test (build domain parameter)
  (cond ((eq domain t) t)
        ((and (consp domain) (eq (car domain) 'eql)) `(eql ,parameter ',(cadr domain)))
        ((member-name domain (build-classes build))
         (record-type-test build domain parameter))
        ((and (symbolp domain) (member-name domain (getf (build-declaration build) :universe)))
         (builtin-type-test build domain parameter))
        (t (fail build 'snowgrave:incomplete-domain :entry-domain
                 (format nil "No sealed class/EQL domain for ~S." domain) :partition))))

(defun infer-function-domains (build)
  "Compute effective helper binding domains from every admitted source caller.
Analysis output is discarded; the ordinary generation pass repeats all source
and class audits with the fixed point. Unknown captures poison the proof."
  (let ((generated (build-generated build)) (constructors (build-constructors build))
        (method-names (build-method-names build)) (sequence (build-sequence build))
        (dependencies (build-dependencies build))
        (*collect-function-flow* t) (*function-flow-changed* nil)
        (iterations 0))
    (setf (build-function-domains build) (make-hash-table :test #'equal)
          (build-function-returns build) (make-hash-table :test #'equal)
          (build-generic-call-shapes build) (make-hash-table :test #'equal))
    (unwind-protect
         (progn
           (dolist (name (getf (build-declaration build) :entries))
             (let* ((form (ordinary-function-form build name))
                    (domains (cadr (assoc name (getf (build-declaration build) :external-domains) :test #'name=))))
               (unless (= (length (ordinary-lambda-list build (caddr form))) (length domains))
                 (fail build 'snowgrave:incomplete-domain :entry-arity
                       (format nil "Entry ~S needs one domain per required argument." name) :partition))
               (setf (gethash (cadr form) (build-function-domains build))
                     (append (copy-tree domains)
                             (make-list (- (length (lambda-input-variables (lambda-contract build (caddr form))))
                                           (length domains))
                                        :initial-element :unknown)))))
           (loop
             (incf iterations)
             (setf *function-flow-changed* nil)
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
             (dolist (name (getf (build-declaration build) :closed-generics)) (emit-generic build name))
             (dolist (form (build-forms build))
               (when (and (eq (defining-kind form) :global) (> (length form) 2))
                 (transform-form build (caddr form) (build-output-package build))))
             (dolist (form (build-forms build))
               (when (eq (defining-kind form) :function)
                 (multiple-value-bind (domains reachedp) (gethash (cadr form) (build-function-domains build))
                   (when reachedp
                     (setf (build-source-key build)
                           (authored-source-key build form))
                     (let ((*argument-domains* nil) (*function-bindings* nil))
                      (multiple-value-bind (scope ordinary)
                          (analyze-lambda-scope build (caddr form) domains :package (build-output-package build)
                                               :specials (body-special-domains (cdddr form)))
                        (declare (ignore ordinary))
                        (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
                          (transform-body build (cdddr form) (build-output-package build))))
                       (let* ((name (cadr form))
                              (previous (gethash name (build-function-returns build) :pending))
                              (additional (lambda-return-summary build (caddr form) domains (cdddr form)))
                              (merged (merge-return-summaries build previous additional)))
                         (unless (same-return-summary-p previous merged)
                           (setf (gethash name (build-function-returns build)) merged
                                 *function-flow-changed* t))))))))
             ;; An unsolved recursive component is not a usable type fact.
             ;; Widen it to unknown and propagate that fact before final audit.
             (unless *function-flow-changed*
               (maphash (lambda (name domains)
                          (when (member :pending domains)
                            (setf (gethash name (build-function-domains build))
                                  (substitute :unknown :pending domains) *function-flow-changed* t))
                          (settle-return-summary build name)) (build-function-domains build))
               (maphash (lambda (name shapes)
                          (declare (ignore name))
                          (maphash (lambda (key domains)
                                     (when (member :pending domains)
                                       (setf (gethash key shapes) (substitute :unknown :pending domains)
                                             *function-flow-changed* t))) shapes))
                        (build-generic-call-shapes build))
               (dolist (name (getf (build-declaration build) :closed-generics))
                 (settle-return-summary build name)))
             (unless *function-flow-changed* (return)))
           (setf (build-function-flow-evidence build)
                 (list :method :finite-argument-binding-fixed-point :iterations iterations
                       :optional-domain-method :effective-call-site-bindings
                       :key-domain-method :first-occurrence-call-site-bindings
                       :primary-return-method :monotone-normal-and-explicit-escape-union
                       :ordered-return-method :same-fixed-point-binding-position-union
                       :generic-return-method :same-emitted-effective-method-proof-tree
                       :generic-binding-method :raw-call-shapes-through-shared-lambda-owner
                       :callable-identity-facts :finite-named-source-target-unions
                       :unresolved-return-domain :unknown
                       :escaping-capture-domain :arbitrary-callers
                       :generic-call-bindings
                       (loop for name in (getf (build-declaration build) :closed-generics)
                             for shapes = (gethash name (build-generic-call-shapes build))
                             collect (list :generic-key (snowgrave::function-name-key name)
                                           :raw-call-shapes
                                           (sort (when shapes
                                                   (loop for key being the hash-keys of shapes using (hash-value domains)
                                                         collect (copy-tree (cons key domains))))
                                                 #'string< :key #'prin1-to-string)))
                       :generic-returns
                       (loop for name in (getf (build-declaration build) :closed-generics)
                             collect (append (list :generic-key (snowgrave::function-name-key name))
                                             (return-summary-evidence (gethash name (build-function-returns build) :unknown))))
                       :functions
                       (sort (loop for name being the hash-keys of (build-function-domains build)
                                   using (hash-value domains)
                                   for contract = (lambda-contract build (caddr (ordinary-function-form build name)))
                                   for required-count = (length (getf contract :required))
                                   for positional-count = (length (lambda-positional-variables contract))
                                   collect (append (list :function-key (snowgrave::function-name-key name)
                                                 :required-domains (copy-tree (subseq domains 0 required-count))
                                                 :optional-domains (copy-tree (subseq domains required-count positional-count))
                                                 :key-domains (mapcar (lambda (spec domain) (list (keyword-name spec) (copy-tree domain)))
                                                                      (getf contract :keys) (nthcdr positional-count domains)))
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
         (let* ((name (cadr form)) (lambda-list (caddr form))
                (domains (gethash name (build-function-domains build)))
                (*argument-domains* nil) (*function-bindings* nil))
          (multiple-value-bind (scope ordinary)
              (analyze-lambda-scope build lambda-list domains :package (build-output-package build)
                                   :specials (body-special-domains (cdddr form)))
           (let* ((*argument-domains* (car scope)) (*function-bindings* (cdr scope))
                  (body (transform-body build (cdddr form) (build-output-package build))))
           (when (member-name name entries)
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
         (when (and (> (length form) 2) (member (cadr form) (source-specials build)))
           (audit-external-shared-value build (cadr form) (caddr form)))
         (push `(,(car form) ,(global-binding-name build (cadr form) (build-output-package build) nil)
                 ,@(when (> (length form) 2)
                     (cons (transform-form build (caddr form) (build-output-package build)) (cdddr form))))
               (build-generated build)))))
    (nreverse entry-records)))

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
           (unless (gethash object seen)
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
               ((or (numberp object) (characterp object) (stringp object) (pathnamep object)) nil)
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
                (dotimes (i (array-total-size object)) (walk (row-major-aref object i))))
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
        (when (boundp symbol) (makunbound symbol))))
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

(defun close-source (source declaration)
  (unless (serializable-tree-p (getf declaration :unit-name))
    (snowgrave::reject 'snowgrave:nonreproducible-source :declaration :unit-identity
                      "Unit identity must contain stable readable scalar/list data."))
  (let* ((identity (getf declaration :unit-name))
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
           (setf (build-source build) (snowgrave:make-authored-source (read-source source) :identity identity))
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
           (setf (build-output-package build) (make-package output-name :use '(:cl)))
           ;; Shared type data is persistent generation state. Establish it
           ;; before the return-domain fixed point takes/discards scratch
           ;; emissions, so a cached name can never outlive its definition.
           (ensure-admitted-layouts build)
           (infer-function-domains build)
           (let* ((dispatch (mapcar (lambda (name) (emit-generic build name))
                                    (getf declaration :closed-generics)))
                  (entries (emit-functions build))
                  (specials (source-specials build))
                  (forms (with-literal-pool build
                           (order-closed-definitions
                            build (mapcar (lambda (form) (declare-closed-specials form specials))
                                          (nreverse (build-generated build))))
                           (build-output-package build)))
                  (metadata (list :abi-version 3 :identity identity :entries entries
                                  :source-normalization
                                  '(:method :sbcl-lexical-host-macroexpansion
                                    :snapshot :once-per-authored-definition
                                    :pass-input :owned-sharing-preserving-graph
                                    :source-keys :authored-definition-position)
                                  :reference-domain (when (build-reference-domain-name build)
                                                      (list :identity identity :schema-source :record-layouts))
                                  :record-layouts (build-layouts build) :dispatch dispatch
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
              (dolist (name (getf declaration :closed-generics))
               (when (typep (fdefinition (mapped-name name (build-output-package build))) 'generic-function)
                 (fail build 'snowgrave:residual-metaobject :generic-root
                       "The second-pass generic binding remains open." :residual-audit)))
             (let ((unit (snowgrave::%make-unit
                          :metadata metadata :source forms :report report
                          :bindings (mapcar (lambda (name)
                                              (cons (snowgrave::function-name-key name)
                                                    (fdefinition (mapped-name name (build-output-package build)))))
                                            (getf declaration :entries)))))
               (publish-special-values special-values)
               (setf (gethash identity-key *published-identities*) t published t)
               unit))))
      (clean-package open)
      (unless published (clean-package (build-output-package build))))))

(snowgrave:register-source-adapter :sbcl #'close-source)
