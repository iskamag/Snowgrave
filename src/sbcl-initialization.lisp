(in-package #:snowgrave.sbcl)

;;;; Receiver-scoped initialization continuation proof. These cells are cold.

(defstruct initialization-phase
  ;; Relational RECORDS are (position key nominal-class origin privacy
  ;; current-class-coverage). Effects and field writes change CURRENT slots;
  ;; they do not restore an origin snapshot or erase exact layout coverage.
  key class slots records aliases relationalp
  (selection :unknown))

(defun initializing-record-domain-p (domain)
  (and (consp domain) (eq (first domain) :initializing-record)
       (snowgrave::source-finite-list-p domain) (= (length domain) 3)
       (symbolp (second domain))
       (or (symbolp (third domain))
           (and (consp (third domain)) (eq (first (third domain)) 'or)
                (snowgrave::source-finite-list-p (third domain)) (every #'symbolp (rest (third domain)))))))

(defun erase-initialization-domain (domain)
  ;; A scoped symbolic receiver is not a singleton, constructor result or
  ;; persistent helper input. Outside its carrier only its nominal class stays.
  (cond ((relational-value-domain-p domain) (erase-initialization-domain (third domain)))
        ((initializing-record-domain-p domain) (third domain))
        ((and (consp domain) (eq (first domain) 'or))
         (cons 'or (mapcar #'erase-initialization-domain (rest domain))))
        (t domain)))

(defun erase-initialization-summary (summary)
  (if (return-summary-p summary)
      (make-return-summary (mapcar #'erase-initialization-domain (return-summary-domains summary))
                           (return-summary-completep summary)) summary))

(defun make-initialization-root-phase (build generic class)
  (let ((layout (find class (build-layouts build) :key (lambda (row) (getf row :class)) :test #'name=)))
    (make-initialization-phase
     :key (gensym "INITIALIZING-RECEIVER") :class class
     ;; Selected callers may already have any value or an unbound slot. Their
     ;; prestate supplies neither native content nor constructor poststate.
     :slots (mapcar (lambda (slot) (list slot nil :external-result)) (getf layout :slots))
     :selection (if (eq generic 'initialize-instance) t :unknown))))

(defun initialization-receiver-domain ()
  (when *initialization-phase*
    (list :initializing-record (initialization-phase-key *initialization-phase*)
          (initialization-phase-class *initialization-phase*))))

(defun initialization-domain-record (domain)
  (when (relational-value-domain-p domain)
    (return-from initialization-domain-record (initialization-domain-record (third domain))))
  (when (and *initialization-phase* (initializing-record-domain-p domain))
    (or (when (eq (second domain) (initialization-phase-key *initialization-phase*))
          (list nil (second domain) (third domain)))
        (find (second domain) (initialization-phase-records *initialization-phase*)
              :key #'second :test #'eq))))

(defun initialization-domain-current-p (domain)
  (not (null (initialization-domain-record domain))))

(defun initialization-field-key (record slot)
  (if (first record) (list :formal (first record) slot) slot))

(defun initialization-field-slot (key)
  (if (and (consp key) (eq (first key) :formal)) (third key) key))

(defun initialization-field-owner-domain (key)
  ;; A field's saved CURRENT owner supplies class coverage, including states
  ;; whose value proof is pending, forgotten, or replaced by a direct store.
  (if (and (consp key) (eq (first key) :formal))
      (let ((record (assoc (second key) (initialization-phase-records *initialization-phase*))))
        (or (sixth record) (third record)))
      (initialization-phase-class *initialization-phase*)))

(defun initialization-record-row (domain)
  (let ((record (initialization-domain-record domain)))
    (when (and record (listp (initialization-phase-slots *initialization-phase*)))
      (list :class (third record)
            :slots (loop for field in (initialization-phase-slots *initialization-phase*)
                         when (if (first record)
                                  (and (consp (first field)) (= (second (first field)) (first record)))
                                  (symbolp (first field)))
                         collect (list (if (first record) (third (first field)) (first field))
                                       (second field) (third field) (fourth field)))))))

(defun copy-initialization-state ()
  (when *initialization-phase* (copy-tree (initialization-phase-slots *initialization-phase*))))

(defun forget-initialization-state ()
  (when (and *initialization-phase* (initialization-phase-relationalp *initialization-phase*))
    (setf *flow-unknown-effect* t))
  (when (and *initialization-phase* (listp (initialization-phase-slots *initialization-phase*)))
    (setf (initialization-phase-slots *initialization-phase*)
          (mapcar (lambda (field) (list (first field) nil :external-result))
                  (initialization-phase-slots *initialization-phase*)))))

(defun join-initialization-states (build left right)
  (when (eq left :no-normal) (return-from join-initialization-states right))
  (when (eq right :no-normal) (return-from join-initialization-states left))
  (unless (and (listp left) (listp right))
    (return-from join-initialization-states :unknown-control))
  (mapcar (lambda (a b)
            (list (first a) (cond ((eq (second a) :pending) (second b))
                                  ((eq (second b) :pending) (second a))
                                  ((eq (second a) (second b)) (second a)))
                  (merge-value-domains build (third a) (third b))
                  (merge-record-field-cases build (initialization-field-slot (first a)) a b
                                            (initialization-field-owner-domain (first a))
                                            (initialization-field-owner-domain (first b))))) left right))

(defun call-with-initialization-state (state process)
  (let ((*initialization-phase* (copy-initialization-phase *initialization-phase*)))
    (setf (initialization-phase-slots *initialization-phase*) (copy-tree state))
    (let ((result (funcall process)))
      (values result (copy-initialization-state)))))

(defun initialization-record-alias-relation (build domain target)
  ;; One alias owner for local stores and instantiated callee effects. Distinct
  ;; formal keys are not automatically distinct runtime objects: the joined
  ;; caller relation is authoritative. Class overlap includes sealed MI rows.
  (let ((record (initialization-domain-record domain)))
    (cond ((and record (eq (second record) (second target))) :must)
          ((and record (first record) (first target))
           (let ((pair (find-if (lambda (pair)
                                 (or (and (= (first pair) (first record)) (= (second pair) (first target)))
                                     (and (= (second pair) (first record)) (= (first pair) (first target)))))
                               (initialization-phase-aliases *initialization-phase*))))
             (third pair)))
          ((member (relational-base domain) '(:pending :unknown :external-result)) :may)
          ((record-flow-domains-overlap-p build domain (third target)) :may))))

(defun phase-slot-update (build receiver slot status value &optional (saved-receiver nil savedp))
  (let* ((domain (if savedp saved-receiver (value-domain build receiver))) (alternatives (domain-alternatives domain))
         (records (or (initialization-phase-records *initialization-phase*)
                      (when (initialization-phase-key *initialization-phase*)
                        (list (list nil (initialization-phase-key *initialization-phase*)
                                    (initialization-phase-class *initialization-phase*)))))))
    (when (and (initialization-phase-relationalp *initialization-phase*)
               (not (every #'initialization-domain-current-p alternatives)))
      (setf *flow-unknown-effect* t))
    (when (listp (initialization-phase-slots *initialization-phase*))
      (dolist (record records)
        (let* ((relations (mapcar (lambda (part) (initialization-record-alias-relation build part record)) alternatives))
               (strongp (and (symbolp receiver) (not (special-variable-p build receiver))
                             (every (lambda (relation) (eq relation :must)) relations)))
               (field (assoc (initialization-field-key record slot)
                             (initialization-phase-slots *initialization-phase*) :test #'equal)))
          (when (and (some #'identity relations) field)
            (set-record-field-cases field nil)
            (if strongp (setf (second field) status (third field) value)
                (setf (second field) (if (eq (second field) status) status nil)
                      (third field) (merge-value-domains build (third field) value)))))))))

(defun initialization-effectful-form-p (build form)
  (and (consp form) (not (member (first form) '(quote function lambda)))
       (or (member (first form) '(call-next-method setf setq incf decf push pop pushnew
                                  slot-makunbound snowgrave::%record-write snowgrave::%record-unbind
                                  funcall apply multiple-value-call make-instance
                                  mapcar mapc mapcan maplist mapl mapcon reduce
                                  find find-if position position-if remove remove-if delete delete-if sort stable-sort merge))
           (member-name (first form) (build-functions build))
           (find-local-function-binding (first form))
           (member-name (first form) (getf (build-declaration build) :closed-generics))
           (some (lambda (part) (initialization-effectful-form-p build part)) (rest form)))))

(defun record-independent-native-place-p (build place local)
  ;; These admitted native setters change one container cell, not a record
  ;; field and cannot invoke user callbacks. Their operands have already run
  ;; through the ordinary place and
  ;; payload audits. No element-value fact is retained here. GETF is different:
  ;; its expansion can replace the enclosing generalized place when it adds a
  ;; property. GETHASH can invoke a table's hash/test functions. Both retain
  ;; the conservative fallback rather than acquiring a purity premise here.
  (and (consp place) (member (first place) '(aref svref bit sbit car cdr))
       (standard-operation-meaning-p build (first place) local)
       (standard-operation-meaning-p build (list 'setf (first place)) local)))

(defun note-initialization-place-write (build place domain &optional (saved-receiver nil savedp) local)
  ;; Called by the existing SETF owner after one storing form has completed,
  ;; before evaluation of the next pair. The value domain is captured at its
  ;; actual RHS evaluation point, after place subforms and before RHS effects.
  (when *initialization-phase*
    (if (and (consp place) (eq (first place) 'slot-value))
        (multiple-value-bind (slot literalp) (quoted-value (third place))
          (if literalp
              (let ((receiver (if savedp saved-receiver (value-domain build (second place)))))
                (note-graph-field-write build place receiver slot t domain)
                (phase-slot-update build (second place) slot t domain receiver))
              (forget-initialization-state)))
        (unless (or (symbolp place) (record-independent-native-place-p build place local))
          (forget-initialization-state)))))

(defun call-with-initialization-default-effects (build name contract process)
  ;; OPTIONAL/KEY initializer syntax is emitted even when a supplied value
  ;; skips its execution. AUX initializers are unconditional and stay ordered.
  (if (and *initialization-phase*
           (member name (append (nthcdr (length (getf contract :required))
                                       (lambda-positional-variables contract))
                                (lambda-key-variables contract))))
      (let ((before (copy-initialization-state)))
        (let ((receipt nil))
         (multiple-value-bind (code omitted-state)
            (call-with-initialization-state before
              (lambda () (multiple-value-bind (code fact) (funcall process)
                           (setf receipt fact) code)))
          (let ((mode (when (and *flow-input-row* (initialization-phase-relationalp *initialization-phase*))
                        (nth (position name (lambda-input-variables contract))
                             (record-flow-input-modes *flow-input-row*)))))
            (setf (initialization-phase-slots *initialization-phase*)
                  (case mode (:omitted omitted-state) (:supplied before)
                        (t (join-initialization-states build before omitted-state)))))
          (values code receipt))))
      (funcall process)))

(defun call-with-initialization-branches (build test then-process else-process &optional local)
  ;; TRANSFORM-FORM owns the source IF syntax and lexical predicates. This
  ;; effect hook only isolates and joins its two normal continuation states.
  (if (null *initialization-phase*)
      (values (funcall then-process) (funcall else-process))
      (let ((before (copy-initialization-state)))
        (multiple-value-bind (yes yes-state)
            (call-with-initialization-state before
              (lambda () (refine-initialization-predicate build test t local) (funcall then-process)))
          (multiple-value-bind (no no-state)
              (call-with-initialization-state before
                (lambda () (refine-initialization-predicate build test nil local) (funcall else-process)))
            (setf (initialization-phase-slots *initialization-phase*)
                  (case (source-truth build test)
                    (:true yes-state) (:false no-state)
                    (t (join-initialization-states build yes-state no-state))))
            (values yes no))))))

(defun refine-initialization-predicate (build test truep local)
  (when (consp test)
    (cond ((and truep (eq (first test) 'and)
                (not (initialization-effectful-form-p build test)))
           (dolist (part (rest test)) (refine-initialization-predicate build part t local)))
          ((and truep (eq (first test) 'integerp) (= (length test) 2)
                (standard-operation-meaning-p build 'integerp local)
                (consp (second test)) (eq (caadr test) 'slot-value)
                (standard-operation-meaning-p build 'slot-value local))
           (let* ((read (second test)) (receiver (second read))
                  (domain (value-domain build receiver)))
             (when (and (symbolp receiver) (not (special-variable-p build receiver))
                        (every #'initialization-domain-current-p (domain-alternatives domain)))
               (multiple-value-bind (slot literalp) (quoted-value (third read))
                 (when literalp (phase-slot-update build receiver slot t 'integer))))))
          ((and (member (first test) '(not null)) (= (length test) 2)
                (standard-operation-meaning-p build (first test) local))
           (refine-initialization-predicate build (second test) (not truep) local))
          ((and (eq (first test) 'slot-boundp) (= (length test) 3)
                (standard-operation-meaning-p build 'slot-boundp local))
           (multiple-value-bind (slot literalp) (quoted-value (third test))
             (when literalp
               (let* ((row (initialization-record-row (value-domain build (second test))))
                      (field (assoc slot (getf row :slots))))
                 (phase-slot-update build (second test) slot (if truep t :unbound)
                                    (if truep (if field (third field) :external-result) :unknown)))))))))

(defun transform-initialization-form (build form emit)
  ;; Source grammar, binders and evaluation order stay in TRANSFORM-FORM.
  ;; This hook contributes only operation effects and conservative boundaries.
  (cond
    ((atom form) (funcall emit))
    ((and (eq (first form) 'call-next-method) (null (rest form)) *initialization-next*)
     (funcall *initialization-next*))
    ((member (first form) '(return-from error throw))
     ;; Source admission still visits trailing forms, but they cannot justify
     ;; the state of an earlier successful nonlocal method exit.
     (let ((code (funcall emit)))
       (setf (initialization-phase-slots *initialization-phase*)
             (if (or (eq (first form) 'throw)
                     (and (eq (first form) 'error) (standard-operation-meaning-p build 'error)))
                 :no-normal :unknown-control))
       code))
    ((member (first form) '(handler-case handler-bind catch tagbody go cond case ecase))
     (forget-initialization-state)
     (let ((*initialization-phase* nil)) (funcall emit)))
    ((member (first form) '(flet labels))
     ;; The body can call the definitions or write through captured aliases.
     ;; No phase effect proof may survive an unsupported helper replay.
     (forget-initialization-state)
     (let ((*initialization-phase* nil)) (funcall emit)))
    ((member (first form) '(lambda function load-time-value))
     (let ((*initialization-phase* nil) (*initialization-next* nil) (*initialization-plan* nil)) (funcall emit)))
    (t
     (let ((unbinding (and (eq (first form) 'slot-makunbound)
                           (nth-value 1 (quoted-value (third form)))))
           (unknown-call-p
             (or (and (symbolp (first form))
                      (or (member-name (first form) (build-functions build))
                          (find-local-function-binding (first form))
                          (member-name (first form) (getf (build-declaration build) :closed-generics))))
                 (member (first form) '(funcall apply multiple-value-call make-instance
                                        mapcar mapc mapcan maplist mapl mapcon reduce
                                        find find-if position position-if remove remove-if delete delete-if
                                        sort stable-sort merge)))))
       (when (and unknown-call-p (not (record-flow-owned-call-p build form)))
         (forget-initialization-state))
       (let ((code (funcall emit)))
         ;; Actual callees run after their arguments. An argument's write
         ;; therefore cannot survive an unproved callee effect on the record.
         (when (and unknown-call-p (not (record-flow-owned-call-p build form)))
         (forget-initialization-state))
         (when unbinding
           (note-graph-field-write build form (value-domain build (second form))
                                   (second (third form)) :unbound :unknown)
           (phase-slot-update build (second form) (second (third form)) :unbound :unknown))
         (when (member (first form) '(incf decf push pushnew pop))
           (note-initialization-place-write
            build (if (member (first form) '(push pushnew)) (third form) (second form))
            (case (first form) ((incf decf) 'number) ((push pushnew) 'cons) (pop :external-result))))
         code)))))

(defun standard-shared-initialization-effect (build)
  (unless (listp (initialization-phase-slots *initialization-phase*))
    (return-from standard-shared-initialization-effect nil))
  (let* ((phase *initialization-phase*)
         (layout (find (initialization-phase-class phase) (build-layouts build)
                       :key (lambda (row) (getf row :class)) :test #'name=))
         (selection (initialization-phase-selection phase)))
    (loop for slot in (getf layout :slots)
          for initializer in (getf layout :slot-initforms)
          for names in (getf layout :slot-initargs)
          for selectedp = (or (eq selection t) (and (listp selection) (member slot selection)))
          for initializedp = (and selectedp initializer)
          do (let ((before (assoc slot (initialization-phase-slots phase))))
               (when (and initializedp (not (eq (second before) t))
                          (initialization-effectful-form-p build (getf initializer :form)))
                 (forget-initialization-state))
               (let* ((current (assoc slot (initialization-phase-slots phase)))
                      (value (if initializedp
                                 (if (eq (second current) :unbound)
                                     (construction-initializer-domain build initializer)
                                     (merge-value-domains build (third current)
                                                          (construction-initializer-domain build initializer)))
                                 (third current))))
                 ;; A normally returning checked supplied/initform write is
                 ;; bound, but an arbitrary selected caller can retain a
                 ;; prebound value or supply an accepted native/private datum.
                 (setf (second current) (if (or (eq (second current) t) initializedp) t (second current))
                       (third current) (if names (merge-value-domains build value :external-result) value)))))))

(defun emit-phase-stock-initialize (build parameters)
  ;; The stock primary delegates to the actual SHARED effective method. The
  ;; same MOP sequence is both emitted and composed; no qualifier order is
  ;; inferred independently and custom SHARED around/after methods remain.
  (let* ((class (initialization-phase-class *initialization-phase*))
         (host (find-class (mapped-name class (build-open-package build))))
         (gf #'shared-initialize)
         (methods (initialization-methods build 'shared-initialize host))
         (arguments (fresh-name build "SHARED-ARGUMENTS"))
         (*cell-domains* (list class t))
         (selection (initialization-phase-selection *initialization-phase*)))
    (unwind-protect
         (progn
           (setf (initialization-phase-selection *initialization-phase*) t)
           (multiple-value-bind (effective options)
               (sb-mop:compute-effective-method gf (sb-mop:generic-function-method-combination gf) methods)
             (when options (fail build 'snowgrave:unsupported-definition :effective-method-options
                                 "Initialization MOP options require normalization." :materialization))
             (let ((validator (emit-argument-validator build 'shared-initialize gf methods)))
               (multiple-value-bind (code proof) (emit-effective build 'shared-initialize effective (list arguments))
                 (values `(let ((,arguments (list* (car ,(first parameters)) t (cdr ,(first parameters)))))
                            (apply #',validator ,arguments) ,code) proof)))))
      (setf (initialization-phase-selection *initialization-phase*) selection))))

(defun emit-initialization-method-call (build generic method next-methods parameters)
  (let ((baseline (assoc generic *standard-initialization-methods*)))
    (when (eq method (second baseline))
      (standard-initialization-method-p build generic method)
      (return-from emit-initialization-method-call
        (if (eq generic 'initialize-instance) (emit-phase-stock-initialize build parameters)
            (let ((code (emit-standard-shared-call build parameters)))
              (standard-shared-initialization-effect build)
              (values code (make-return-summary (list (third (initialization-receiver-domain))) t)))))))
  (let* ((name (fresh-name build "METHOD"))
         (form (authored-method build generic method))
         (initial (copy-initialization-state))
         (next-called-p nil) (proof :pending))
    (unless form (fail build 'snowgrave:unsupported-definition :method-provenance
                       "The selected initialization method has no authored source." :materialization))
    (with-build-source-key (build (method-source-key build generic method form))
      (multiple-value-bind (qualifiers lambda-list body) (method-parts form)
        (declare (ignore qualifiers))
        (let* ((*argument-domains* nil) (*function-bindings* nil)
               (*local-function-frames* nil) (*value-domain-local-functions* nil) (*immediate-lambda-domains* nil)
               (*generated-class-operation* (typep method 'sb-mop:standard-accessor-method))
               (*current-method* (list generic method (not (null next-methods)) :pending))
               (*initialization-next*
                 (when next-methods
                   (lambda ()
                     (setf next-called-p t)
                     (multiple-value-bind (code summary)
                         (emit-initialization-continuation build generic next-methods parameters)
                       (setf (fourth *current-method*)
                             (if (return-summary-p summary) summary
                                 (let ((*effective-return-proof* t)) (form-return-summary build summary))))
                       code))))
               (domains (method-binding-domains build generic lambda-list body)))
          (if (initialization-phase-relationalp *initialization-phase*)
              (setf domains (record-flow-body-domains domains))
              (setf (first domains) (initialization-receiver-domain)))
          ;; Return proof uses the input snapshot, never the later poststate.
          ;; Missing continuation facts remain conservative, not a value proof.
          (unless (initialization-phase-relationalp *initialization-phase*)
           (setf proof (erase-initialization-summary
                       (if (and *collect-function-flow* (member :pending domains)) :pending
                           (lambda-return-summary build lambda-list domains body :method t)))))
          (multiple-value-bind (scope ordinary)
              (analyze-lambda-scope build lambda-list domains :package (build-output-package build)
                                   :method t :specials (body-special-domains body) :original parameters)
            (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
              (push name (build-method-names build))
              (let ((declarations (loop while (and body (consp (first body)) (eq (caar body) 'declare))
                                        collect (transform-form build (pop body) (build-output-package build)))))
                (multiple-value-bind (code receipt)
                    (transform-body build body (build-output-package build) :original parameters)
                  (when (initialization-phase-relationalp *initialization-phase*)
                    ;; Analyze every selected body and dependency now, but a
                    ;; not-yet-known caller cannot publish its provisional
                    ;; value/effect state into the monotone return join.
                    (setf proof (if (and *collect-function-flow* (member :pending domains)) :pending receipt)))
                  (push `(defun ,name ,parameters
                           ,(fixed-effective-method-body
                             build generic method ordinary
                             (append (when (source-specials build) (list `(declare (special ,@(source-specials build)))))
                                     declarations (list `(block ,(if (consp generic) (second generic) generic) ,@code)))
                             parameters))
                        (build-generated build)))))))))
    (when (and next-methods (not next-called-p))
      ;; Retain selected tail obligations even if the authored method skips
      ;; its continuation. Its effects do not reach the caller in that case.
      (call-with-initialization-state initial
        (lambda () (emit-effective build generic `(call-method ,(first next-methods) ,(rest next-methods)) parameters))))
    (values `(,name ,@parameters) (if (eq proof :pending) '(error) proof))))


(defstruct initialization-continuation input name proof output pass)
(defstruct initialization-plan
  (continuations (make-hash-table :test #'equal))
  (pass 0) changedp)

(defun emit-initialization-continuation (build generic methods parameters)
  ;; One emitted tail per MOP continuation per pass. CALL-NEXT sites join
  ;; actual incoming states, then the same CEM is replayed until they settle.
  ;; A duplicated next call therefore shares code, including down long chains.
  (let* ((key (cons generic methods))
         (table (initialization-plan-continuations *initialization-plan*))
         (owner (or (gethash key table)
                    (setf (gethash key table) (make-initialization-continuation))))
         (incoming (copy-initialization-state))
         (old (initialization-continuation-input owner))
         (joined (if old (join-initialization-states build old incoming) incoming))
         (pass (initialization-plan-pass *initialization-plan*)))
    (unless (equal old joined)
      (setf (initialization-continuation-input owner) joined
            (initialization-plan-changedp *initialization-plan*) t))
    (unless (eql pass (initialization-continuation-pass owner))
      (let ((name (fresh-name build "NEXT"))
            (*initialization-phase* (copy-initialization-phase *initialization-phase*)))
        (setf (initialization-phase-slots *initialization-phase*) (copy-tree joined))
        (multiple-value-bind (code proof)
            (emit-effective build generic `(call-method ,(first methods) ,(rest methods)) parameters)
          (setf (initialization-continuation-name owner) name
                (initialization-continuation-proof owner) proof
                (initialization-continuation-output owner) (copy-initialization-state)
                (initialization-continuation-pass owner) pass)
          (push name (build-method-names build))
          (push `(defun ,name ,parameters ,code) (build-generated build)))))
    (setf (initialization-phase-slots *initialization-phase*)
          (copy-tree (initialization-continuation-output owner)))
    (values `(,(initialization-continuation-name owner) ,@parameters)
            (initialization-continuation-proof owner))))

(defun emit-initialization-plan (build generic effective parameters)
  (let ((*initialization-plan* (make-initialization-plan))
        (initial (copy-initialization-state))
        (generated (build-generated build)) (constructors (build-constructors build))
        (methods (build-method-names build)) (sequence (build-sequence build))
        (dependencies (build-dependencies build)))
    (loop for pass from 1 do
      (setf (initialization-plan-pass *initialization-plan*) pass
            (initialization-plan-changedp *initialization-plan*) nil
            (initialization-phase-slots *initialization-phase*) (copy-tree initial)
            (build-generated build) generated (build-constructors build) constructors
            (build-method-names build) methods (build-sequence build) sequence
            (build-dependencies build) dependencies)
      (multiple-value-bind (code proof) (emit-effective build generic effective parameters)
        (unless (initialization-plan-changedp *initialization-plan*)
          (return-from emit-initialization-plan (values code proof)))))))
