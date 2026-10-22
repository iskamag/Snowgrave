(in-package #:snowgrave.sbcl)

;;;; Cold relational facts share the ordinary argument/return fixed point.
;;;; Formal positions are source roles. No activation key leaves a carrier.

;; DOMAINS are the ordinary nominal input tuple. Each RECORD is
;; (position fields original-provenance may-private-p current-class-coverage).
;; FIELDS begin with the same (slot boundness value-domain) unconditional
;; facts used by actual slot reads; an optional fourth item holds class views.
;; Coverage is (:record-view-classes exact-layout ...), :PENDING bottom, or
;; :UNKNOWN. In particular the empty finite set is not an unknown owner.
;; The privacy envelope distinguishes a real fresh shell from an ordinary
;; disjoint nominal cell even after its activation identity is erased.
(defstruct (record-flow-input (:constructor make-record-flow-input (domains records aliases &optional modes)))
  domains records aliases modes)

(defun flow-input-domains (input)
  (if (record-flow-input-p input) (record-flow-input-domains input) input))

(defun relational-value-domain-p (domain)
  (and (consp domain) (eq (first domain) :relational-value)
       (snowgrave::source-finite-list-p domain) (= (length domain) 3)))

(defun relational-base (domain)
  (cond ((relational-value-domain-p domain) (relational-base (third domain)))
        ((and (consp domain) (eq (first domain) 'or))
         (cons 'or (mapcar #'relational-base (rest domain))))
        (t domain)))

(defun merge-record-flow-effects (build left right)
  (cond ((equal left right) left)
        ((or (eq left :unowned) (eq right :unowned)) :unowned)
        ((or (eq left :havoc) (eq right :havoc)) :havoc)
        (t (merge-record-flow-rows build left right))))

(defun merge-record-flow-fields (build left right left-domain right-domain)
  ;; Preserve the existing key order and append only new keys. Retaining the
  ;; last occurrence would reorder an unchanged union on each caller join.
  (loop for slot in (remove-duplicates (append (mapcar #'first left) (mapcar #'first right)) :from-end t)
        for a = (assoc slot left) for b = (assoc slot right)
        collect (list slot (and a b (cond ((eq (second a) :pending) (second b))
                                           ((eq (second b) :pending) (second a))
                                           ((eq (second a) (second b)) (second a))))
                      (if (and a b) (merge-value-domains build (third a) (third b)) :external-result)
                      (merge-record-field-cases build slot a b left-domain right-domain))))

(defun merge-record-flow-rows (build left right &optional left-domains right-domains)
  (loop for index in (remove-duplicates (append (mapcar #'first left) (mapcar #'first right)) :from-end t)
        for a = (assoc index left) for b = (assoc index right)
        collect (list index
                      (cond ((and a b) (merge-record-flow-fields
                                       build (second a) (second b)
                                       (record-flow-row-view-domain build a (nth index left-domains))
                                       (record-flow-row-view-domain build b (nth index right-domains))))
                            ;; A wholly pending argument has contributed no
                            ;; possible record state yet. Its missing row is
                            ;; bottom, unlike a known argument without proof.
                            ((and (null a) (eq (nth index left-domains) :pending)) (second b))
                            ((and (null b) (eq (nth index right-domains) :pending)) (second a))
                            (t (mapcar (lambda (field) (list (first field) nil :external-result))
                                       (second (or a b)))))
                      (cond ((and (third a) (third b)) (merge-value-domains build (third a) (third b)))
                            ((and (null a) (eq (nth index left-domains) :pending)) (third b))
                            ((and (null b) (eq (nth index right-domains) :pending)) (third a))
                            ((or (third a) (third b)) (relational-base (third (or a b)))))
                      (or (fourth a) (fourth b))
                      (merge-record-view-domains
                       build (record-flow-row-view-domain build a (nth index left-domains))
                       (record-flow-row-view-domain build b (nth index right-domains))))))

(defun record-flow-identity (domain)
  (cond ((initializing-record-domain-p domain) (list :activation (second domain)))
        ((graph-node-domain-p domain) (list :capture (second domain)))
        ((relational-value-domain-p domain) (record-flow-identity (third domain)))))

(defun flow-record-domain-p (build domain)
  (and (not (member domain '(:pending :unknown :external-result)))
       (record-domain-p build domain)))

(defun normalize-record-flow-domain (domain arguments)
  ;; Field self/peer edges refer to finite formal roles, never copied keys.
  (let* ((base (relational-base domain)) (identity (record-flow-identity base))
         (position (and identity (position identity arguments :key #'record-flow-identity :test #'equal))))
    (cond (position (list :relational-value (list :argument position) (erase-initialization-domain base)))
          ((initializing-record-domain-p base) (third base))
          ((and (consp base) (eq (first base) 'or))
           (cons 'or (mapcar (lambda (part) (normalize-record-flow-domain part arguments)) (rest base))))
          (t base))))

(defun record-flow-field-facts (build domain)
  ;; Capture rows supply keys and schema, not mutable entry values. All value
  ;; and boundness premises come through the same effective field read owner.
  (let* ((parts (domain-alternatives (relational-base domain)))
         (rows (mapcar (lambda (part) (private-record-slot-row build part)) parts)))
    (when (every #'identity rows)
      (loop with fields = nil with owner-domain = :pending
            for part in parts for row in rows
            for current = (loop for field in (getf row :slots)
                                collect (multiple-value-bind (status value presentp cases)
                                            (record-slot-entry-fact build part (first field))
                                          (declare (ignore presentp))
                                          (let ((fact (list (first field) status value cases)))
                                            (set-record-field-cases fact (record-field-cases build (first field) fact part)))))
            do (setf fields (if fields (merge-record-flow-fields build fields current owner-domain part) current)
                     owner-domain (merge-value-domains build owner-domain part))
            finally (return fields)))))

(defun record-flow-entry-fields (build domain arguments)
  (when (flow-record-domain-p build domain)
    (mapcar (lambda (field)
              (list (first field) (second field)
                    (normalize-record-flow-domain (third field) arguments)
                    (map-record-field-cases (fourth field)
                                            (lambda (value) (normalize-record-flow-domain value arguments)))))
            (record-flow-field-facts build domain))))

(defun record-flow-domains-overlap-p (build left right)
  ;; Two incomparable superclasses can share a sealed multiple-inheritance
  ;; subclass. Only the existing closed layout universe establishes disjointness.
  (some (lambda (layout)
          (and (subtype-domain-p build (getf layout :class) (private-record-domain-base left))
               (subtype-domain-p build (getf layout :class) (private-record-domain-base right))))
        (build-layouts build)))

(defun record-flow-domain-alias-relation (build left right)
  (let ((relations
          (loop for a in (domain-alternatives left) append
                (loop for b in (domain-alternatives right)
                      for ai = (record-flow-identity a) for bi = (record-flow-identity b)
                      for target = (initialization-domain-record b)
                      collect (cond (target (initialization-record-alias-relation build a target))
                                    ((and ai bi (equal ai bi)) :must)
                                    ((and ai bi (eq (first ai) :capture) (eq (first bi) :capture)) nil)
                                    ((record-flow-domains-overlap-p build a b) :may))))))
    (cond ((every (lambda (relation) (eq relation :must)) relations) :must)
          ((some #'identity relations) :may))))

(defun make-call-record-flow-input (build domains &optional modes)
  (let ((records nil) (aliases nil))
    (loop for domain in domains for i from 0
          when (flow-record-domain-p build domain) do
            (let ((fields (record-flow-entry-fields build domain domains)))
              ;; A nominal caller contributes an unknown entry view, including
              ;; unbound fields. It can never borrow another caller's row.
              (unless fields
                (let ((slots (remove-duplicates
                              (loop for class in (record-view-classes build domain)
                                    for layout = (find class (build-layouts build)
                                                       :key (lambda (row) (getf row :class)) :test #'name=)
                                    append (getf layout :slots)))))
                  (setf fields (mapcar (lambda (slot) (list slot nil :external-result)) slots))))
              (setf fields (mapcar (lambda (field)
                                    (append (subseq field 0 3)
                                            (list (record-field-cases build (first field) field domain)))) fields))
              (push (list i fields (persistent-record-flow-domain domain)
                          (graph-private-record-domain-p build domain) (record-view-domain build domain)) records))
          do (loop for other in domains for j from 0 when (< i j) do
               (when (and (flow-record-domain-p build domain) (flow-record-domain-p build other))
                 (let ((relation (record-flow-domain-alias-relation build domain other)))
                   (when relation (push (list i j relation) aliases))))))
    (make-record-flow-input (mapcar (lambda (domain)
                                           (if (flow-record-domain-p build domain)
                                               (value-domain-shape build (relational-base domain))
                                               (erase-initialization-domain (relational-base domain)))) domains)
                            (nreverse records) (nreverse aliases) modes)))

(defun join-record-flow-inputs (build previous additional)
  (let* ((old (flow-input-domains previous)) (new (flow-input-domains additional))
         (domains (mapcar (lambda (a b) (merge-value-domains build a b)) old new))
         (records (remove-if-not
                   (lambda (record) (flow-record-domain-p build (nth (first record) domains)))
                   (merge-record-flow-rows build (when (record-flow-input-p previous) (record-flow-input-records previous))
                                           (when (record-flow-input-p additional) (record-flow-input-records additional))
                                           old new)))
         (aliases
           (loop for pair in (remove-duplicates
                              (append (mapcar (lambda (row) (subseq row 0 2)) (when (record-flow-input-p previous) (record-flow-input-aliases previous)))
                                      (mapcar (lambda (row) (subseq row 0 2)) (when (record-flow-input-p additional) (record-flow-input-aliases additional))))
                              :test #'equal :from-end t)
                 for a = (find pair (when (record-flow-input-p previous) (record-flow-input-aliases previous)) :key (lambda (row) (subseq row 0 2)) :test #'equal)
                 for b = (find pair (when (record-flow-input-p additional) (record-flow-input-aliases additional)) :key (lambda (row) (subseq row 0 2)) :test #'equal)
                 when (and (assoc (first pair) records) (assoc (second pair) records))
                   collect (append pair
                                   (list (cond ((and (null a) (some (lambda (i) (eq (nth i old) :pending)) pair)) (third b))
                                               ((and (null b) (some (lambda (i) (eq (nth i new) :pending)) pair)) (third a))
                                               ((and a b (eq (third a) :must) (eq (third b) :must)) :must)
                                               (t :may)))))))
    (make-record-flow-input
     domains records aliases
     (loop for a in (when (record-flow-input-p previous) (record-flow-input-modes previous))
           for b in (when (record-flow-input-p additional) (record-flow-input-modes additional))
           collect (if (eq a b) a :maybe)))))

(defun record-flow-domain-covered-p (build actual expected)
  ;; Type coverage cannot establish the selector premise of an input edge.
  (if (relational-value-domain-p expected)
      (and (relational-value-domain-p actual) (equal (second actual) (second expected))
           (record-flow-domain-covered-p build (third actual) (third expected)))
      (flow-domain-covered-p build (relational-base actual) expected)))

(defun same-record-flow-input-p (left right)
  (and (equal (flow-input-domains left) (flow-input-domains right))
       (equal (when (record-flow-input-p left) (record-flow-input-modes left))
              (when (record-flow-input-p right) (record-flow-input-modes right)))
       (equal (when (record-flow-input-p left) (record-flow-input-records left))
              (when (record-flow-input-p right) (record-flow-input-records right)))
       (equal (when (record-flow-input-p left) (record-flow-input-aliases left))
              (when (record-flow-input-p right) (record-flow-input-aliases right)))))

(defun record-flow-input-covered-p (build actual expected)
  (and (every (lambda (a b) (flow-domain-covered-p build a b))
              (flow-input-domains actual) (flow-input-domains expected))
       (every (lambda (actual expected) (or (eq expected :maybe) (eq actual expected)))
              (record-flow-input-modes actual) (record-flow-input-modes expected))
       ;; The emitted body may depend on MUST identity or the absence of a
       ;; MAY edge. Both are caller obligations, not collector assumptions.
       (every (lambda (pair)
                (let ((allowed (find (subseq pair 0 2) (record-flow-input-aliases expected)
                                     :key (lambda (row) (subseq row 0 2)) :test #'equal)))
                  (and allowed (or (eq (third allowed) :may) (eq (third pair) :must)))))
              (record-flow-input-aliases actual))
       (every (lambda (pair)
                (or (eq (third pair) :may)
                    (equal pair (find (subseq pair 0 2) (record-flow-input-aliases actual)
                                      :key (lambda (row) (subseq row 0 2)) :test #'equal))))
              (record-flow-input-aliases expected))
       (every (lambda (record)
                (let* ((actual-row (assoc (first record) (record-flow-input-records actual)))
                       (actual-fields (second actual-row)))
                  (and (or (not (fourth actual-row)) (fourth record))
                       (or (null (fifth record))
                           (record-view-domain-covered-p build
                                                         (record-flow-row-view-domain build actual-row
                                                                                      (nth (first record) (flow-input-domains actual)))
                                                         (fifth record)))
                       (or (null (third record))
                           (flow-domain-covered-p build (third actual-row) (third record)))
                   (every (lambda (field)
                           (let ((a (or (assoc (first field) actual-fields)
                                        (list (first field) nil :external-result))))
                             ;; A union row's missing-slot placeholder proves
                             ;; no presence or value. Presence checks still
                             ;; use every actual layout, not this envelope.
                             (and (or (null (second field)) (eq (second a) (second field)))
                                  (record-flow-domain-covered-p build (third a) (third field))
                                  (record-field-cases-covered-p build a field
                                                               (record-flow-row-view-domain
                                                                build actual-row (nth (first record) (flow-input-domains actual)))))))
                         (second record)))))
              (record-flow-input-records expected))))

(defun make-record-flow-phase (build input)
  (let ((records nil) (slots nil))
    (dolist (row (record-flow-input-records input))
      (let* ((position (first row)) (domain (nth position (record-flow-input-domains input)))
             (class (value-domain-shape build domain)) (key (gensym "FORMAL-RECEIVER"))
             (view-domain (record-flow-row-view-domain build row domain))
             (classes (record-view-classes build view-domain))
             (exact-class (when (and classes (null (rest classes))) (first classes))))
        (push (list position key class (third row) (fourth row) view-domain) records)
        (dolist (field (second row))
          (push (list (list :formal position (first field)) (second field)
                      (list :relational-value
                            (append (list :field position (first field)) (when exact-class (list exact-class)))
                            (third field))
                      (mapcar (lambda (entry)
                                (list (first entry) (second entry)
                                      (list :relational-value
                                            (list :field position (first field) (first entry)) (third entry))))
                              (fourth field))) slots))))
    (make-initialization-phase :key nil :class nil :slots (nreverse slots)
                               :records (nreverse records) :aliases (record-flow-input-aliases input)
                               :relationalp t)))

(defun instantiate-formal-entry-domain (domain)
  (cond ((relational-value-domain-p domain)
         (let ((selector (second domain)))
           (if (eq (first selector) :argument)
               (let ((record (assoc (second selector) (initialization-phase-records *initialization-phase*))))
                 (if record (list :initializing-record (second record) (third record)) (third domain)))
               (list :relational-value selector (instantiate-formal-entry-domain (third domain))))))
        ((and (consp domain) (eq (first domain) 'or))
         (cons 'or (mapcar #'instantiate-formal-entry-domain (rest domain))))
        (t domain)))

(defun call-with-record-flow-input (build input process)
  (if (not (and (graph-state-profile-p build) (record-flow-input-p input)))
      (funcall process (flow-input-domains input))
      (let* ((*flow-input-row* input)
             (*flow-unknown-effect* nil)
             (*flow-value-receipts* nil)
             (*initialization-phase* (make-record-flow-phase build input))
             (*flow-record-origins* (initialization-phase-records *initialization-phase*))
             (*initialization-next* nil) (*initialization-plan* nil)
             (domains (copy-tree (record-flow-input-domains input))))
        (dolist (record (initialization-phase-records *initialization-phase*))
          (setf (nth (first record) domains) (list :initializing-record (second record) (third record))))
        ;; Resolve finite peer/self edges only after every formal is present.
        (dolist (field (initialization-phase-slots *initialization-phase*))
          (setf (third field) (instantiate-formal-entry-domain (third field))
                (fourth field) (map-record-field-cases (fourth field) #'instantiate-formal-entry-domain)))
        (funcall process domains))))

(defun publish-record-flow-domain (domain)
  (cond ((and (initializing-record-domain-p domain) *flow-input-row*)
         (let ((record (find (second domain) (initialization-phase-records *initialization-phase*) :key #'second :test #'eq)))
           (if record (list :relational-value (list :argument (first record)) (third domain)) (third domain))))
        ((relational-value-domain-p domain)
         (list :relational-value (second domain) (erase-initialization-domain (third domain))))
        ((and (consp domain) (eq (first domain) 'or)) (cons 'or (mapcar #'publish-record-flow-domain (rest domain))))
        (t domain)))

(defun record-flow-poststate ()
  (if *flow-unknown-effect* :havoc
      (if (listp (initialization-phase-slots *initialization-phase*))
          (loop for record in (initialization-phase-records *initialization-phase*)
                collect (list (first record)
                              (loop for field in (initialization-phase-slots *initialization-phase*)
                                    when (and (consp (first field)) (= (second (first field)) (first record)))
                                    collect (list (third (first field)) (second field)
                                                  (publish-record-flow-domain (third field))
                                                  (map-record-field-cases (fourth field) #'publish-record-flow-domain)))
                                (third record) nil (sixth record)))
          :havoc)))

(defun publish-record-flow-summary (summary)
  (if (return-summary-p summary)
      (make-return-summary (mapcar #'publish-record-flow-domain (return-summary-domains summary))
                           (return-summary-completep summary) (record-flow-poststate))
      summary))

(defun flow-receipt-summary (build form)
  (let ((receipt (and (consp form) (assoc form *flow-value-receipts* :test #'eq))))
    (if receipt (cdr receipt) (form-return-summary-code build form))))

(defun record-flow-owned-call-p (build form)
  (and (consp form) (not (initialization-generic-p (first form)))
       (or (and (symbolp (first form)) (not (find-local-function-binding (first form)))
                (or (ordinary-function-form build (first form))
                    (member-name (first form) (getf (build-declaration build) :closed-generics))))
           (and (member (first form) '(funcall apply multiple-value-call))
                (multiple-value-bind (targets globals callee-domain) (known-function-targets build (second form))
                  ;; A callback producer still at bottom needs the same
                  ;; pending receipt as an unsolved direct source callee.
                  (or (eq (relational-base callee-domain) :pending)
                      (and targets
                           (every (lambda (target)
                                    (and (not (local-function-binding-p target))
                                         (member-name target globals)
                                         (not (initialization-generic-p target))
                                         (or (ordinary-function-form build target)
                                             (member-name target (getf (build-declaration build) :closed-generics)))))
                                  targets))))))))

(defun pending-record-flow-state ()
  (when (listp (initialization-phase-slots *initialization-phase*))
    (setf (initialization-phase-slots *initialization-phase*)
          (mapcar (lambda (field) (list (first field) :pending :pending))
                  (initialization-phase-slots *initialization-phase*)))))

(defun substitute-record-flow-domain (domain arguments entry-fields)
  (cond ((relational-value-domain-p domain)
         (let* ((selector (second domain)) (position (second selector)))
           (case (first selector)
             (:argument (or (nth position arguments) :unknown))
             (:field (let ((field (assoc (third selector) (second (assoc position entry-fields)))))
                       (if field
                           (let ((entry (and (fourth selector)
                                             (assoc (fourth selector) (fourth field) :test #'name=))))
                             (if entry (third entry) (third field))) :external-result)))
             (t (third domain)))))
        ((and (consp domain) (eq (first domain) 'or))
         (cons 'or (mapcar (lambda (part) (substitute-record-flow-domain part arguments entry-fields)) (rest domain))))
        (t domain)))

(defun live-record-flow-fields (build arguments)
  (loop for domain in arguments for index from 0
        for fields = (record-flow-field-facts build domain)
        when fields collect (list index fields)))

(defun apply-record-flow-effects (build effects arguments before)
  ;; A nonlocal/unsupported control state has no normal row to update.
  ;; A later syntactic call cannot resurrect facts across that boundary.
  (unless (listp (initialization-phase-slots *initialization-phase*))
    (return-from apply-record-flow-effects nil))
  (cond ((member effects '(:unowned :havoc)) (forget-initialization-state))
        (t
         ;; Resolve against one saved input, then join all formal aliases at
         ;; each target. An OR/may-alias argument permits only a weak update.
         (let ((updates nil)
               (targets (or (initialization-phase-records *initialization-phase*)
                            (when (initialization-phase-key *initialization-phase*)
                              (list (list nil (initialization-phase-key *initialization-phase*)
                                          (initialization-phase-class *initialization-phase*)))))))
           (dolist (record effects)
             (let* ((actual (nth (first record) arguments)) (alternatives (domain-alternatives actual)))
               (dolist (target targets)
                 (let* ((relations (mapcar (lambda (part) (initialization-record-alias-relation build part target)) alternatives))
                        (strongp (every (lambda (relation) (eq relation :must)) relations))
                        (possiblep (some #'identity relations))
                        (target-domain (or (sixth target) (third target))))
                   (when possiblep
                     (dolist (field (second record))
                       (let* (;; The callee joined every reached layout. An
                              ;; effect on this target concerns only its saved
                              ;; CURRENT class coverage, just as method input
                              ;; projection does. Peer selectors still retain
                              ;; their own source-class qualifiers below.
                              (effect (select-record-field-view build field target-domain))
                              (key (initialization-field-key target (first field)))
                              (prior (assoc key (initialization-phase-slots *initialization-phase*) :test #'equal))
                              (status (second effect))
                              (value (substitute-record-flow-domain (third effect) arguments before))
                              (cases (mapcar (lambda (entry)
                                               (list (first entry) (second entry)
                                                     (substitute-record-flow-domain (third entry) arguments before)))
                                             (fourth effect)))
                              (old (assoc key updates :test #'equal)))
                         (when (and prior (not strongp))
                           (setf cases (merge-record-field-cases build (first field) prior
                                                                (list (first field) status value cases)
                                                                target-domain target-domain))
                           (setf status (if (eq status (second prior)) status nil)
                                 value (merge-value-domains build value (third prior))))
                         (when prior
                           (if old
                               (setf (second old) (if (eq (second old) status) status nil)
                                     (third old) (merge-value-domains build (third old) value)
                                     (fourth old) (merge-record-field-cases build (first field) old
                                                                           (list (first field) status value cases)
                                                                           target-domain target-domain))
                               (push (list key status value cases) updates))))))))))
           (dolist (update updates)
             (let ((field (assoc (first update) (initialization-phase-slots *initialization-phase*) :test #'equal)))
               (when field
                 (setf (second field) (second update) (third field) (third update))
                 (set-record-field-cases field (fourth update)))))))))

(defun record-flow-call-receipt (build form)
  "Apply the settled contract after actual arguments, branching finite callees."
  (multiple-value-bind (targets globals callee-domain)
      (if (member (first form) '(funcall apply multiple-value-call))
          (known-function-targets build (second form)) (values (list (first form)) nil))
    (when (eq (relational-base callee-domain) :pending)
      (pending-record-flow-state)
      (return-from record-flow-call-receipt :pending))
    (multiple-value-bind (arguments bindings completep variable-tail pendingp)
        (if (member (first form) '(funcall apply multiple-value-call))
            (ordinary-call-argument-plan build form) (values (rest form) nil t nil))
      (unless completep
        (when pendingp
          (pending-record-flow-state)
          (return-from record-flow-call-receipt :pending))
        (forget-initialization-state)
        (return-from record-flow-call-receipt (make-return-summary (list :external-result) nil)))
      (let* ((*argument-domains* (append bindings *argument-domains*)) (*flow-deferred-call-p* t)
             (domains (mapcar (lambda (argument) (value-domain build argument)) arguments))
             (before (live-record-flow-fields build domains)) (initial (copy-initialization-state))
             (proof :pending) (output :no-normal))
        (dolist (target targets)
          (multiple-value-bind (returned state)
              (call-with-initialization-state
               initial
               (lambda ()
                 (audit-function-call build target arguments :variable-tail variable-tail)
                 (audit-generic-call-shape build target arguments nil variable-tail)
                 (let ((summary (source-call-return-summary build target globals t)))
                   (cond ((eq summary :pending) (pending-record-flow-state) :pending)
                         ((return-summary-p summary)
                          (let ((result (make-return-summary
                                         (mapcar (lambda (domain) (substitute-record-flow-domain domain domains before))
                                                 (return-summary-domains summary))
                                         (return-summary-completep summary))))
                            (apply-record-flow-effects build (return-summary-effects summary) domains before) result))
                         (t (forget-initialization-state) (make-return-summary (list :external-result) nil))))))
            (setf proof (merge-return-summaries build proof returned)
                  output (join-initialization-states build output state))))
        (setf (initialization-phase-slots *initialization-phase*) output)
        proof))))

(defun call-with-transformed-value-receipt (build form process)
  (let ((outer *flow-value-receipts*) (receipt nil) (code nil))
    (let ((*flow-value-receipts* nil))
      (setf code (funcall process))
      (when (and (consp form) (eq (first form) 'return-from))
        (push (flow-receipt-summary build (third form)) *flow-exit-receipts*))
      (setf receipt (if (record-flow-owned-call-p build form)
                        (record-flow-call-receipt build form)
                        ;; Child receipts were captured at their value points.
                        ;; No expression is reexecuted or queried under a later
                        ;; row merely to reconstruct its returned value.
                        (form-return-summary-code build form))))
    (when (consp form)
      ;; Authored source is allowed to share conses across occurrence sites.
      ;; An EQ lookup must overapproximate those values, never silently take
      ;; a later occurrence's fact as the earlier PROG1 value.
      (let ((previous (assoc form outer :test #'eq)))
        (setf *flow-value-receipts*
              (acons form (if previous (merge-return-summaries build (cdr previous) receipt) receipt)
                     (remove form outer :key #'car :test #'eq)))))
    (values code receipt)))

(defun record-flow-body-domains (domains)
  (let ((result (copy-tree domains)))
    (dolist (record (initialization-phase-records *initialization-phase*))
      (when (< (first record) (length result))
        (setf (nth (first record) result) (list :initializing-record (second record) (third record)))))
    result))

(defun analyze-record-flow-function (build form input)
  "Audit/emit the single ordinary body under the joined entry row."
  (let ((*argument-domains* nil) (*function-bindings* nil)
        (*local-function-frames* nil) (*value-domain-local-functions* nil)
        (*immediate-lambda-domains* nil) (*flow-exit-receipts* nil))
    (call-with-record-flow-input
     build input
     (lambda (domains)
       (multiple-value-bind (scope ordinary)
           (analyze-lambda-scope build (third form) domains :package (build-output-package build)
                                :specials (body-special-domains (cdddr form)))
         (let ((*argument-domains* (car scope)) (*function-bindings* (cdr scope)))
           (multiple-value-bind (code receipt) (transform-body build (cdddr form) (build-output-package build))
             (values code
                     (if (and (record-flow-input-p input) (graph-state-profile-p build))
                         (publish-record-flow-summary
                          (reduce (lambda (a b) (merge-return-summaries build a b))
                                  *flow-exit-receipts* :initial-value receipt))
                         ;; Ordinary final emission already repeats the
                         ;; source/callback audits. Only inference needs this
                         ;; separate nonrelational return query; a redundant
                         ;; post-emission analysis has no consumer.
                         (when *collect-function-flow*
                           (lambda-return-summary build (third form) domains (cdddr form))))
                     ordinary))))))))

(defun record-flow-positional-inputs (input)
  (loop for domain in (flow-input-domains input) for position from 0
        collect (if (assoc position (when (record-flow-input-p input) (record-flow-input-records input)))
                    (list :relational-value (list :argument position) domain) domain)))

(defun project-record-flow-input (build input projected)
  (let ((positions (mapcar (lambda (domain)
                             (when (and (relational-value-domain-p domain)
                                        (eq (first (second domain)) :argument))
                               (second (second domain)))) projected)))
    (labels ((rename (domain)
               (cond ((relational-value-domain-p domain)
                      (let* ((selector (second domain)) (position (position (second selector) positions)))
                        (if position
                            (list :relational-value (cons (first selector) (cons position (cddr selector)))
                                  (rename (third domain)))
                            (relational-base (third domain)))))
                     ((and (consp domain) (eq (first domain) 'or)) (cons 'or (mapcar #'rename (rest domain))))
                     (t domain))))
      (make-record-flow-input
       (mapcar #'relational-base projected)
       (loop for source in positions for position from 0
             for row = (when source (assoc source (record-flow-input-records input)))
             when row collect (list position (mapcar (lambda (field)
                                                       (let ((narrowed (select-record-field-view
                                                                         build field (nth position projected)
                                                                         (nth position *cell-domains*)
                                                                         (nth position *cell-axis-domains*))))
                                                         (list (first narrowed) (second narrowed) (rename (third narrowed))
                                                               (map-record-field-cases (fourth narrowed) #'rename))))
                                                     (second row)) (third row) (fourth row)
                                    (select-record-view-domain
                                     build (record-flow-row-view-domain build row (nth source (flow-input-domains input)))
                                     (nth position projected) (nth position *cell-domains*)
                                     (nth position *cell-axis-domains*))))
       (loop for a in positions for i from 0 append
             (loop for b in positions for j from 0
                   for pair = (when (and a b (< i j)) (if (= a b) (list a b :must)
                                  (find-if (lambda (pair) (or (and (= a (first pair)) (= b (second pair)))
                                                            (and (= b (first pair)) (= a (second pair)))))
                                           (record-flow-input-aliases input))))
                   when pair collect (list i j (third pair))))))))

(defun original-record-flow-row (build domain)
  ;; Unsupported control may forget local transfer while still retaining an
  ;; independently proved captured/family entry origin. A fresh initializer
  ;; shell's origin is only a class, so it supplies no normal-poststate facts.
  (let ((record (and (initializing-record-domain-p domain)
                     (find (second domain) *flow-record-origins* :key #'second :test #'eq))))
    (when (and record (fourth record))
      (private-record-slot-row build (fourth record)))))

(defun pending-record-flow-effects-p (effects)
  (and (listp effects)
       (some (lambda (record)
               (some (lambda (field) (or (eq (second field) :pending)
                                         (eq (third field) :pending)
                                         (some (lambda (entry) (or (eq (second entry) :pending)
                                                                   (eq (third entry) :pending))) (fourth field))))
                     (second record))) effects)))

(defun persistent-record-flow-domain (domain)
  (cond ((initializing-record-domain-p domain)
         (let ((record (find (second domain) *flow-record-origins* :key #'second :test #'eq)))
           (if (and record
                    (every (lambda (part) (or (graph-node-domain-p part) (owned-record-domain-p part)))
                           (domain-alternatives (fourth record))))
               (fourth record) (third domain))))
        ((relational-value-domain-p domain) (persistent-record-flow-domain (third domain)))
        ((and (consp domain) (eq (first domain) 'or))
         (cons 'or (mapcar #'persistent-record-flow-domain (rest domain))))
        (t domain)))

(defun active-initialization-shell-p (domain)
  (cond ((initializing-record-domain-p domain)
         (let ((record (find (second domain) *flow-record-origins* :key #'second :test #'eq)))
           (not (and record (or (graph-node-domain-p (fourth record)) (owned-record-domain-p (fourth record)))))))
        ((relational-value-domain-p domain) (active-initialization-shell-p (third domain)))
        ((and (consp domain) (eq (first domain) 'or)) (some #'active-initialization-shell-p (rest domain)))))

(defun independent-record-flow-domain-p (build domain)
  ;; This query runs with the local state carrier absent. Stable captured or
  ;; normal-family facts and an already proved logical record type survive;
  ;; no scoped receiver identity, state snapshot or unowned origin does.
  (every (lambda (part)
           (and (not (initializing-record-domain-p part))
                (not (relational-value-domain-p part))
                (or (graph-node-domain-p part) (owned-record-domain-p part)
                    (member-name part (build-classes build)))))
         (domain-alternatives domain)))

(defun independent-record-flow-result-domain (build domain)
  (cond ((or (eq domain :pending) (native-data-domain-p build domain)
             (independent-record-flow-domain-p build domain)) domain)
        ;; A proved global function identity does not depend on the removed
        ;; record-state carrier. Keeping it proves neither native data nor
        ;; permission to publish the callable at an observable boundary.
        ((let ((name (domain-function-target domain)))
           (and name (snowgrave::source-name-p name) (function-target-p build name nil))) domain)
        ((and (consp domain) (eq (first domain) 'or))
         (reduce (lambda (left right) (merge-value-domains build left right))
                 (mapcar (lambda (part) (independent-record-flow-result-domain build part)) (rest domain))
                 :initial-value :pending))
        ;; A normal-return geometry proof is independent of native contents.
        ;; Keep only that product; never bless aggregate elements or aliases.
        ((subtype-domain-p build domain '(or list vector)) (qualify-domain-origin domain :external-result))
        (t :external-result)))
