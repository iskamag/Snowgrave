(in-package #:snowgrave.sbcl)

(defparameter *reproducible-cold-operations*
  ;; Read-only, non-registry primitives and fresh list/vector construction.
  ;; Integer arithmetic has the shared, argument-qualified identity owner.
  '(values values-list list list* cons vector car cdr caar cadr cdar cddr
    first second third fourth rest nth nthcdr endp null not atom consp
    symbolp numberp integerp rationalp floatp realp complexp stringp characterp
    vectorp arrayp eq eql equal equalp identity append copy-list copy-tree
    symbol-name keywordp char-code code-char))

(defparameter *reproducible-cold-macros*
  ;; These are source expanders, not permission to execute their resulting
  ;; operations. The shared transformer still checks every expanded effect.
  (loop for name in '(lambda and or when unless cond case ecase typecase etypecase
                       destructuring-bind multiple-value-bind multiple-value-setq
                       push pop pushnew incf decf setf prog1 prog2 loop do do*
                       dolist dotimes return rotatef shiftf sb-int:quasiquote)
        for function = (macro-function name)
        when function collect (cons name function)))

(defun reject-cold-recipe (build detail)
  (fail build 'snowgrave:nonreproducible-source :method-combination-recipe
        detail :source-admission))

(defun cold-source-nodes (form)
  ;; Provenance only: no evaluation, call interpretation or inferred effect.
  ;; The host walker chooses which of these nodes occur as executable source.
  (let ((nodes (make-hash-table :test #'eq)) (pending (list form)))
    (loop while pending for node = (pop pending) do
      (unless (gethash node nodes)
        (setf (gethash node nodes) t)
        (when (consp node) (push (car node) pending) (push (cdr node) pending))))
    nodes))

(defun audit-cold-recipe-macro (build form environment)
  (when (and (consp form)
             ;; These leaves are interpreted by the existing CEM composer,
             ;; never expanded through a host macro function.
             (not (and *effective-method-emitter*
                       (member (car form) '(call-method sb-pcl::call-method-list)))))
    (when (member (car form) '(macrolet symbol-macrolet))
      (reject-cold-recipe build "A cold local macro needs its own reproducible expansion proof."))
    (let ((function (and (symbolp (car form)) (macro-function (car form) environment))))
      (when (and function (not (eq function (cdr (assoc (car form) *reproducible-cold-macros*)))))
        (reject-cold-recipe build (format nil "Cold macro ~S has no pinned reproducible source expansion." (car form)))))))

(defun cold-lexical-variable-p (build name)
  (and (symbolp name) (assoc name *argument-domains*)
       (not (special-variable-p build name)) (not (member name *declared-specials*))))

(defun cold-primitive-p (build name local)
  (let ((native (assoc name *native-ordinary-functions*)))
    (and (member name *reproducible-cold-operations*)
         (standard-operation-meaning-p build name local)
         native (fboundp name) (eq (fdefinition name) (cdr native)))))

(defun audit-cold-source-function (build name)
  ;; One transient source/effect proof per definition, not a callable/value
  ;; cache. Recursive edges share the same effect obligation; actual cold
  ;; execution is neither elided nor replayed from a saved result.
  (let* ((definition (snowgrave:find-authored-definition (build-source build) :function name))
         (form (and definition (snowgrave:authored-definition-form definition))))
    (unless form (reject-cold-recipe build "A cold call lacks authored helper source."))
    (unless (gethash form *cold-recipe-functions*)
      (setf (gethash form *cold-recipe-functions*) :checking)
      (with-build-source-key (build (authored-source-key build form))
        (let ((*argument-domains* nil) (*function-bindings* nil)
              (*local-function-frames* nil) (*value-domain-local-functions* nil)
              (*immediate-lambda-domains* nil) (*mutable-invariant-bindings* nil)
              (*local-function-scope-cache* nil) (*immediate-callee-value* nil)
              (*flow-value-receipts* nil) (*flow-exit-receipts* nil) (*flow-input-row* nil)
              (*flow-record-origins* nil) (*cell-domains* nil)
              (*generated-class-operation* nil) (*effective-return-proof* nil)
              (*declared-specials* nil) (*current-method* nil) (*tagbody-targets* nil)
              (*initialization-phase* nil) (*initialization-next* nil) (*initialization-plan* nil)
              (*effective-method-emitter* nil) (*cold-recipe-source-nodes* nil)
              (*cold-recipe-normalization* t) (*cold-recipe-active* t))
          (transform-form build
                          (normalize-source-expression build `(lambda ,(third form) ,@(cdddr form)))
                          (build-open-package build) :open t)))
      (setf (gethash form *cold-recipe-functions*) :checked))))

(defun audit-cold-recipe-target (build target local &optional arguments globalp)
  (cond ((local-function-binding-p target) t)
        ((and (consp target) (eq (first target) 'lambda)) t)
        ((and (not globalp) (find-local-function-binding target)) t)
        ((ordinary-function-form build target) (audit-cold-source-function build target))
        ((cold-primitive-p build target local) t)
        ((and arguments (reproducible-integer-operation-p build target local)
              (every (lambda (argument) (subtype-domain-p build (value-domain build argument) 'integer)) arguments)) t)
        (t (reject-cold-recipe build
                              (format nil "Cold operation ~S has no stable nonmutating recipe contract." target)))))

(defun audit-cold-recipe-reference (build reference local)
  (cond ((and (consp reference) (member (first reference) '(function lambda))
              (consp (second reference)) (eq (caadr reference) 'lambda)) t)
        ((and (consp reference) (eq (first reference) 'lambda)) t)
        (t (multiple-value-bind (targets globals) (known-function-targets build reference)
             (unless targets (reject-cold-recipe build "An unknown cold callback cannot establish reproducible effects."))
             (dolist (target targets)
               (audit-cold-recipe-target build target local nil (member-name target globals)))))))

(defun audit-cold-recipe-form (build form local)
  ;; Grammar, evaluation order and lexical scopes belong to TRANSFORM-FORM.
  ;; This hook contributes only the cold recipe's read/write/call obligations.
  (cond
    ((symbolp form)
     (unless (or (member form '(nil t)) (keywordp form) (cold-lexical-variable-p build form))
       (reject-cold-recipe build (format nil "Cold read of free or dynamic variable ~S is not reproducible." form))))
    ((atom form) nil)
    ((eq (first form) 'quote) nil)
    ((eq (first form) 'declare)
     (dolist (declaration (rest form))
       (unless (member (first declaration) '(ignore ignorable optimize dynamic-extent))
         (reject-cold-recipe build "This cold declaration lacks an independent native type/effect contract."))))
    ((eq (first form) 'the)
     (unless (native-value-type-p (second form))
       (reject-cold-recipe build "A cold THE cannot invoke an ambient type expander.")))
    ((member (first form) '(setq setf))
     (loop for tail on (cdr form) by #'cddr for place = (car tail) do
       (unless (cold-lexical-variable-p build place)
         (reject-cold-recipe build "A cold recipe may assign only its own lexical variables."))))
    ((member (first form) '(push pop))
     (unless (cold-lexical-variable-p build (if (eq (first form) 'push) (third form) (second form)))
       (reject-cold-recipe build "A cold list stack may update only its own lexical binding.")))
    ((member (first form) '(incf decf pushnew multiple-value-setq))
     (reject-cold-recipe build "This cold update has no proved stable lexical transfer contract."))
    ((member (first form) '(if cond case ecase when unless and or progn locally
                           block return-from tagbody go let let* flet labels lambda
                           multiple-value-bind multiple-value-prog1)) nil)
    ((eq (first form) 'function)
     (unless (and (consp (second form)) (eq (caadr form) 'lambda))
       (audit-cold-recipe-target build (or (find-local-function-binding (second form)) (second form)) local)))
    ((member (first form) '(funcall apply multiple-value-call))
     (audit-cold-recipe-reference build (second form) local))
    ((member (first form) '(mapcar mapc maplist mapl))
     (let ((native (assoc (first form) *native-ordinary-functions*)))
       (unless (and native (standard-operation-meaning-p build (first form) local)
                    (fboundp (first form)) (eq (fdefinition (first form)) (cdr native)))
         (reject-cold-recipe build "A cold mapping operation lacks its actual native meaning.")))
     (audit-cold-recipe-reference build (second form) local))
    (t (audit-cold-recipe-target build (first form) local (rest form)))))

(defun audit-cold-method-group-predicates (build form)
  ;; Patterns are declarative host syntax. A symbol predicate is the one
  ;; executable reference synthesized from that syntax by the host expander.
  (dolist (group (fourth form))
    (when (special-variable-p build (first group))
      (reject-cold-recipe build "A cold method group cannot use a dynamic variable binding."))
    (loop for pattern in (rest group)
          until (member pattern '(:description :order :required))
          when (and (symbolp pattern) pattern (not (eq pattern '*)))
            do (audit-cold-recipe-target build pattern nil))))
