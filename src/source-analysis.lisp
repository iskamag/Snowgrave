(in-package #:snowgrave)

(defun source-name-p (name)
  (or (and (symbolp name) (symbol-package name))
      (and (consp name) (eq (car name) 'setf) (consp (cdr name)) (null (cddr name))
           (symbolp (cadr name)) (symbol-package (cadr name)))))

(defun source-name-key (name)
  "Stable definition identity in the source environment, independent of execution domains."
  (unless (source-name-p name)
    (error "A definition key requires an interned function name."))
  (if (consp name) (list 'setf (source-name-key (cadr name)))
      (list (package-name (symbol-package name)) (symbol-name name))))

(defun source-defining-kind (form)
  (when (and (consp form) (symbolp (car form)))
    ;; Explicit source units own ordinary CL definitions as well as the thin
    ;; recording wrappers. A wrapper marker is not additional language proof.
    (cond ((member (car form) '(defclass cl:defclass)) :class)
          ((member (car form) '(defgeneric cl:defgeneric)) :generic)
          ((member (car form) '(defmethod cl:defmethod)) :method)
          ((member (car form) '(define-method-combination cl:define-method-combination))
           :method-combination)
          ((eq (car form) 'cl:defun) :function)
          ((member (car form) '(defvar defparameter defconstant)) :global))))

(defstruct (authored-definition (:constructor %make-authored-definition))
  (kind nil :read-only t) (name nil :read-only t)
  (form nil :read-only t) (position 0 :read-only t))

(defstruct (authored-source (:constructor %make-authored-source))
  (forms nil :read-only t) (index nil :read-only t))

(defun make-authored-source (forms &key identity copy-observer)
  "Own and index ordered authored input. Readers expose immutable facts by contract.
The complete definition sequence is ordered; per-kind groups are newest first.
Repeated ordinary definitions reject; methods retain their observable source order."
  (unless (handler-case (not (null (list-length forms))) (type-error () nil))
    (reject 'nonreproducible-source :source-admission :source-sequence
            "Authored input must be a finite proper list of ordered definitions."
            :path (list identity)))
  (let ((owned (immutable-copy forms copy-observer)) (index (make-hash-table :test #'equal)))
    (setf (gethash :by-form index) (make-hash-table :test #'eq))
    (loop for form in owned for position from 1
          for kind = (source-defining-kind form)
          for name = (and (consp form) (cadr form))
          for source-key = (list identity position) do
      (unless kind
        (reject 'unsupported-definition :source-admission :top-level-form
                "The source owner needs an authored definition with reproducible provenance."
                :source-key source-key :path (list identity)))
      (unless (and (source-name-p name)
                   (or (symbolp name) (member kind '(:function :generic :method))))
        (reject 'nonreproducible-source :source-admission :definition-identity
                "An authored definition needs a stable interned source name."
                :source-key source-key :path (list identity)))
      (let ((key (list :definition kind (source-name-key name))))
        (when (and (not (eq kind :method)) (gethash key index))
          (reject 'nonreproducible-source :source-admission :redefinition
                  "Repeated ordinary authored definitions need explicit sealing semantics."
                  :source-key source-key :path (list identity)))
        (let ((definition (%make-authored-definition :kind kind :name name :form form :position position)))
          (setf (gethash key index) definition)
          (setf (gethash form (gethash :by-form index)) definition)
          (push definition (gethash :definitions index))
          (push definition (gethash (list :definitions kind) index))
          (push name (gethash (list :names kind) index))
          (push form (gethash (list :forms kind) index))
          (when (member (car form) '(defvar defparameter)) (push name (gethash :specials index))))))
    (setf (gethash :definitions index) (nreverse (gethash :definitions index))
          (gethash :specials index) (nreverse (gethash :specials index)))
    (%make-authored-source :forms owned :index index)))

(defun authored-source-definitions (source &optional kind)
  (gethash (if kind (list :definitions kind) :definitions) (authored-source-index source)))
(defun authored-source-names (source kind)
  (gethash (list :names kind) (authored-source-index source)))
(defun authored-source-kind-forms (source kind)
  (gethash (list :forms kind) (authored-source-index source)))
(defun authored-source-specials (source)
  (gethash :specials (authored-source-index source)))
(defun find-authored-definition (source kind name)
  (when (source-name-p name)
    (gethash (list :definition kind (source-name-key name)) (authored-source-index source))))
(defun authored-form-definition (source form)
  (gethash form (gethash :by-form (authored-source-index source))))

(defun authored-form-position (source form)
  (let ((definition (authored-form-definition source form)))
    (unless definition (error "The form is not owned by this authored source."))
    (authored-definition-position definition)))

(defun source-body-special-domains (body)
  (loop for form in body when (and (consp form) (eq (car form) 'declare))
        append (loop for declaration in (cdr form)
                     when (and (consp declaration) (eq (car declaration) 'special))
                       append (mapcar (lambda (name) (cons name :unknown)) (cdr declaration)))))

(defun source-body-parts (body)
  (let ((prefix nil) (documentationp nil))
    (loop
      (cond ((and (consp (car body)) (eq (caar body) 'declare)) (push (pop body) prefix))
            ((and (not documentationp) (stringp (car body)) (cdr body))
             (setf documentationp t) (push (pop body) prefix))
            (t (return))))
    (values (nreverse prefix) body)))

(defun source-block-body (name body)
  ;; DEFUN/DEFMETHOD are renamed into disposable/output namespaces. Retain
  ;; their authored implicit block, without renaming explicit lexical blocks.
  (multiple-value-bind (prefix executable) (source-body-parts body)
    (append prefix (list `(block ,(if (consp name) (cadr name) name) ,@executable)))))


(defun source-finite-list-p (value)
  (handler-case (not (null (list-length value))) (type-error () nil)))

(defun source-lambda-contract (lambda-list &key specialized-required-p source-key path)
  "Validate ordinary bindings; only authored methods admit required specializers.
SPECIALIZED-REQUIRED-P admits exact (variable specializer) required bindings and
normalizes those bindings to variables. Ordinary function/lambda/local bindings
must never inherit this normalization."
  (labels ((invalid (feature detail)
             (reject 'unsupported-definition :source-admission feature detail :source-key source-key :path path))
           (variablep (value)
             (and (symbolp value) (not (keywordp value)) (not (member value '(nil t)))
                  (not (member value lambda-list-keywords)))))
   (unless (source-finite-list-p lambda-list)
     (invalid :lambda-list-contract "An ordinary lambda list must be a finite proper list."))
   (let ((state :required) required optional rest keys aux variables keyp allow ordinary)
    (dolist (item lambda-list)
      (cond ((member item '(&optional &rest &key &allow-other-keys &aux))
             (unless (case item
                       (&optional (eq state :required))
                       (&rest (member state '(:required :optional)))
                       (&key (member state '(:required :optional :after-rest)))
                       (&allow-other-keys (eq state :key))
                       (&aux (member state '(:required :optional :after-rest :key :after-key))))
               (invalid :lambda-list-contract "Lambda-list markers must occur once, in ordinary binding order."))
             (push item ordinary)
             (case item
               (&optional (setf state :optional))
               (&rest (setf state :rest))
               (&key (setf state :key keyp t))
               (&allow-other-keys (setf allow t state :after-key))
               (&aux (setf state :aux))))
            ((member item lambda-list-keywords)
             (reject 'unsupported-definition :source-admission :lambda-list-contract
                   "Only ordinary required/optional/rest/key/aux argument contracts are admitted." :source-key source-key :path path))
            (t
             (when (and (eq state :required) (consp item))
               (unless (and specialized-required-p (source-finite-list-p item) (= (length item) 2)
                            (or (symbolp (second item))
                                (and (source-finite-list-p (second item)) (= (length (second item)) 2)
                                     (eq (car (second item)) 'eql))))
                 (invalid :lambda-list-required "An ordinary required argument must be a variable; only a method admits an exact specialized pair.")))
             (when (and (eq state :rest) (not (symbolp item)))
               (invalid :lambda-list-rest "A rest argument must be one symbol variable."))
             (when (eq state :after-key)
               (invalid :lambda-list-key "Only &AUX may follow &ALLOW-OTHER-KEYS."))
             (let* ((head (if (consp item) (car item) item))
                    (variable (if (and (eq state :key) (consp head)) (cadr head) head)))
               (unless (variablep variable)
                 (invalid :lambda-list-variable "A closed ordinary argument binding must have a nonconstant symbol variable."))
               (when (consp item)
                 (unless (and (source-finite-list-p item)
                              (<= 1 (length item) (if (eq state :aux) 2 3)))
                   (invalid :lambda-list-binding "An argument binding needs a finite supported initializer/supplied-p shape.")))
               (when (and (eq state :key) (consp head))
                 (unless (and (source-finite-list-p head) (= (length head) 2) (symbolp (first head)))
                   (invalid :lambda-list-key "A renamed keyword binding needs a keyword name and variable.")))
               (when (member variable variables)
                 (invalid :lambda-list-variable "An ordinary lambda list cannot bind the same variable twice."))
               (push variable variables)
               (when (and (member state '(:optional :key)) (consp item) (= (length item) 3))
                 (unless (and (variablep (third item)) (not (member (third item) variables)))
                   (invalid :lambda-list-variable "A supplied-p binding needs a distinct nonconstant symbol variable."))
                 (push (third item) variables))
               (case state
                 (:required (push variable required) (push variable ordinary))
                 (:optional (push item optional) (push item ordinary))
                 (:rest (setf rest variable state :after-rest) (push variable ordinary))
                 (:after-rest (reject 'unsupported-definition :source-admission :lambda-list-rest
                                    "A rest binding must be followed by a lambda-list marker." :source-key source-key :path path))
                 (:key (push item keys) (push item ordinary))
                 (:aux (push item aux) (push item ordinary)))))))
    (when (eq state :rest)
      (invalid :lambda-list-rest "&REST needs one symbol variable."))
    (list :required (nreverse required) :optional (nreverse optional) :rest rest
          :keys (nreverse keys) :keyp keyp :allow allow :aux (nreverse aux)
          :variables (nreverse variables) :ordinary (nreverse ordinary)))))

(defun analyze-source-lambda-bindings (lambda-list scope analyze bind &key specialized-required-p source-key path)
  "Own ordinary lambda initializer order and lexical scope, without owning facts.
ANALYZE receives (name initializer prior-scope), returning a fact and processed
initializer. BIND receives (name kind initializer-fact prior-scope), returning
a persistent extended scope. Kinds are :REQUIRED, :OPTIONAL, :REST, :KEY, :AUX
and :SUPPLIED-P; only :AUX necessarily takes its value from the initializer.
Return the body scope, rewritten ordinary lambda list and ordered processed
initializers. Later bindings are absent from earlier initializer scopes."
  (let ((contract (source-lambda-contract lambda-list :specialized-required-p specialized-required-p
                                        :source-key source-key :path path))
        (state :required) (result nil) (initializers nil))
    (dolist (item (getf contract :ordinary))
      (cond ((member item lambda-list-keywords)
             (push item result)
             (case item
               (&optional (setf state :optional)) (&rest (setf state :rest))
               (&key (setf state :key)) (&aux (setf state :aux))))
            ((member state '(:optional :key :aux))
             (let* ((head (if (consp item) (car item) item))
                    (name (if (consp head) (second head) head))
                    (initializer (if (consp item) (second item) nil)))
               (multiple-value-bind (fact processed) (funcall analyze name initializer scope)
                 (push processed initializers)
                 (setf scope (funcall bind name state fact scope))
                 (when (and (member state '(:optional :key)) (consp item) (third item))
                   (setf scope (funcall bind (third item) :supplied-p nil scope)))
                 (push (if (consp item) (list* head processed (cddr item)) item) result))))
            (t (setf scope (funcall bind item state nil scope)) (push item result))))
    (values scope (nreverse result) (nreverse initializers))))

(defun analyze-source-bindings (bindings sequential-p scope analyze extend &key source-key path)
  "Share LET/LET* initializer order and scope extension across source analyses.
ANALYZE receives (name initializer initializer-scope), returning a fact and a
processed initializer. EXTEND receives (name fact prior-scope) and must preserve
the prior scope, returning a new version. The result is
the body scope and source-ordered (name processed-initializer) pairs. Scope and
facts belong to the calling analysis; this operation owns no type/call domain."
  (labels ((proper-list-p (value)
             (handler-case (not (null (list-length value))) (type-error () nil)))
           (invalid (feature detail)
             (reject 'unsupported-definition :source-admission feature detail
                     :source-key source-key :path path)))
    (unless (proper-list-p bindings)
      (invalid :binding-sequence "LET bindings must form a finite proper list."))
    (let ((initial-scope scope) (body-scope scope) (processed nil))
      (dolist (binding bindings)
        (unless (or (symbolp binding)
                    (and (proper-list-p binding) (<= 1 (length binding) 2)))
          (invalid :binding-shape "A LET binding needs a variable and at most one initializer."))
        (let ((name (if (consp binding) (car binding) binding))
              (initializer (if (consp binding) (second binding) nil)))
          (unless (and (symbolp name) (not (keywordp name)) (not (member name '(nil t))))
            (invalid :binding-variable "A LET binding needs a nonconstant symbol variable."))
          (multiple-value-bind (fact result)
              (funcall analyze name initializer (if sequential-p body-scope initial-scope))
            (setf body-scope (funcall extend name fact body-scope))
            (push (list name result) processed))))
      (values body-scope (nreverse processed)))))

(defun source-required-binding-variables (pattern &key nested source-key path)
  "Inventory every variable in flat required bindings or nested required patterns.
Optional/key/rest/whole destructuring needs its own complete contract. No nested
variable may inherit an outer scope's type or callable proof."
  (labels ((invalid (feature detail)
             (reject 'unsupported-definition :source-admission feature detail
                     :source-key source-key :path path))
           (walk (part &optional ancestors)
             (when (member part ancestors :test #'eq)
               (invalid :destructuring-shape "Nested binding patterns must be acyclic."))
             (unless (handler-case (not (null (list-length part))) (type-error () nil))
               (invalid :destructuring-shape "Required binding patterns must be finite proper lists."))
             (mapcan (lambda (item)
                       (cond ((and nested (listp item)) (walk item (cons part ancestors)))
                             ((and (symbolp item) (not (keywordp item))
                                   (not (member item '(nil t))) (not (member item lambda-list-keywords)))
                              (list item))
                             (t (invalid :destructuring-contract
                                         "This pattern needs complete variable/default/error normalization.")))) part)))
    (walk pattern)))

(defun analyze-source-multiple-value-bindings (variables producer scope analyze extend &key source-key path)
  "Analyze the producer in the original scope, then bind every result in parallel.
ANALYZE returns ordered opaque binding-position facts, the processed producer,
and a complete count flag. A proved prefix is usable without a complete count;
its facts must already account for possible ordinary NIL padding. EXTEND
receives (name kind fact prior-scope), where KIND is
:PROVIDED, :MISSING (ordinary NIL padding), or :UNKNOWN. No facts or tuple
representation are owned here. The caller must not infer a missing position
from an incomplete count."
  (let ((names (source-required-binding-variables variables :source-key source-key :path path)))
    (unless (= (length names) (length (remove-duplicates names)))
      (reject 'unsupported-definition :source-admission :multiple-value-bindings
              "MULTIPLE-VALUE-BIND cannot bind a variable twice." :source-key source-key :path path))
    (multiple-value-bind (facts processed completep) (funcall analyze producer scope)
      (unless (source-finite-list-p facts)
        (reject 'unsupported-definition :source-admission :multiple-value-facts
                "A multiple-value analysis must return finite ordered facts." :source-key source-key :path path))
      (loop for name in names for tail = facts then (cdr tail)
            for kind = (cond (tail :provided) (completep :missing) (t :unknown))
            do (setf scope (funcall extend name kind (car tail) scope)))
      (values scope processed))))
