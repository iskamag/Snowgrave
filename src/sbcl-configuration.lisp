(in-package #:snowgrave.sbcl)

;;;; Cold graph capture and materialization facts.
(defparameter *standard-graph-slot-methods*
  (loop for operation in '(sb-mop:slot-value-using-class sb-mop:slot-boundp-using-class)
        collect (cons operation
                      (multiple-value-bind (methods certainp)
                          (sb-mop:compute-applicable-methods-using-classes
                           (fdefinition operation)
                           (mapcar #'find-class '(standard-class standard-object
                                                  sb-mop:standard-effective-slot-definition)))
                        (unless certainp (error "No standard graph slot protocol."))
                        (mapcar (lambda (method) (cons method (sb-mop:method-function method))) methods)))))

(defparameter *standard-graph-inspectors*
  (loop for operation in '(sb-mop:class-name sb-mop:class-finalized-p
                           sb-mop:class-direct-superclasses sb-mop:class-direct-slots
                           sb-mop:class-slots sb-mop:class-precedence-list
                           sb-mop:slot-definition-name sb-mop:slot-definition-type
                           sb-mop:slot-definition-allocation sb-mop:slot-definition-location)
        for function = (fdefinition operation)
        collect (list operation function
                      (mapcar (lambda (method) (cons method (sb-mop:method-function method)))
                              (sb-mop:generic-function-methods function)))))

(defun graph-inspect (build operation object)
  ;; EQL-specialized hooks on the *source* class/slot are not exercised by the
  ;; disposable class pass. Prove stock class-only access before invoking one.
  (let* ((baseline (assoc operation *standard-graph-inspectors*))
         (function (second baseline)))
    (unless (and (eq function (fdefinition operation))
                 (standard-class-applicability-p function))
      (fail build 'snowgrave:unclosed-class-operation :graph-inspection-protocol
            "Source graph introspection needs unchanged standard class-only MOP access." :graph-capture))
    (multiple-value-bind (methods certainp)
        (sb-mop:compute-applicable-methods-using-classes function (list (class-of object)))
      (unless (and certainp methods
                   (every (lambda (method)
                            (let* ((expected (assoc method (third baseline)))
                                   (source (and expected (sb-introspect:find-definition-source (cdr expected))))
                                   (path (and source (sb-introspect:definition-source-pathname source))))
                              (and expected (eq (sb-mop:method-function method) (cdr expected))
                                   (typep path 'logical-pathname) (string= (host-namestring path) "SYS")))) methods))
        (fail build 'snowgrave:unclosed-class-operation :graph-inspection-protocol
              "A source graph metaobject has custom or value-sensitive introspection semantics." :graph-capture)))
    (funcall function object)))

(defun graph-source-instance-p (value)
  ;; TYPEP on an obsolete CLOS instance can run UPDATE-INSTANCE before capture
  ;; even asks for a slot. Classify its raw storage instead of repairing it.
  (and (sb-kernel:%instancep value)
       (sb-kernel::standard-classoid-p
        (sb-kernel:layout-classoid (sb-kernel:%instance-layout value)))))

(defun graph-source-node (build value)
  (gethash value (build-graph-index build)))

(defun graph-array-geometry-matches-p (array row)
  (and (arrayp array)
       (equal (array-dimensions array) (getf row :dimensions))
       (let ((options (getf row :options)))
         (and (equal (array-element-type array) (getf options :element-type))
              (eq (not (null (adjustable-array-p array))) (getf options :adjustable))
              (eq (not (null (array-has-fill-pointer-p array)))
                  (not (null (member :fill-pointer options))))
              (or (not (array-has-fill-pointer-p array))
                  (eql (fill-pointer array) (getf options :fill-pointer)))))))

(defun graph-literal-origin (build value)
  "Join owned literal copies only when they still describe the captured node."
  (let* ((origin (gethash value (build-source-origins build) value))
         (row (graph-source-node build origin)))
    (unless row (return-from graph-literal-origin value))
    (unless (or (eq value origin) (gethash value (build-graph-literal-states build)))
      ;; A destructive macro can change its owned input. Lineage alone must
      ;; neither discard that edit nor apply it to the original configuration.
      ;; Compare each copied node once; active entries close native cycles.
      (setf (gethash value (build-graph-literal-states build)) :active)
      (flet ((same-edge (copy expected)
               (let ((origin (gethash expected (build-source-origins build) expected)))
                 (if (graph-source-node build origin)
                     (eq (graph-literal-origin build copy) origin)
                     (eql copy origin)))))
        (unless
            (cond
              ((consp origin)
               (and (consp value)
                    (same-edge (car value) (first (getf row :values)))
                    (same-edge (cdr value) (second (getf row :values)))))
              ((arrayp origin)
               (and (graph-array-geometry-matches-p value row)
                    (multiple-value-bind (parent offset) (array-displacement value)
                      (and (= offset (getf row :offset))
                           (if (getf row :backing)
                               (and parent (same-edge parent (getf row :backing)))
                               (and (null parent)
                                    (or (null (array-element-type value))
                                        (if (getf row :import-reference)
                                            (let ((baseline (getf row :literal-baseline)))
                                              (and baseline
                                                   (loop for index below (array-total-size value)
                                                         always (same-edge (row-major-aref value index)
                                                                           (row-major-aref baseline index)))))
                                            (loop for element in (getf row :values) for index from 0
                                                  always (same-edge (row-major-aref value index) element))))))))))
              (t nil))
          (fail build 'snowgrave:nonreproducible-source :graph-literal-provenance
                "An owned literal alias was changed during normalization and no longer matches its captured configuration node."
                :graph-capture)))
      (setf (gethash value (build-graph-literal-states build)) :complete))
    origin))

(defun graph-scalar-domain (value)
  ;; Snapshot values seed transition analysis; mutable scalars are not EQL facts.
  (cond ((integerp value) 'integer) ((numberp value) 'number)
        ((symbolp value) 'symbol) ((characterp value) 'character)
        (t :unknown)))

(defun graph-row-fact (row)
  (list :graph-node (getf row :id) (getf row :domain)))

(defun graph-value-fact (build value)
  (let ((row (graph-source-node build value)))
    (if row (graph-row-fact row) (graph-scalar-domain value))))

(defun validate-graph-source-instance (build value)
  "Validate source storage and class/slot interpretation before reading fields."
  (let* ((wrapper (sb-kernel:%instance-layout value))
         (class (sb-kernel:classoid-pcl-class (sb-kernel:layout-classoid wrapper))))
    (unless (and class (eq (class-of class) (find-class 'standard-class))
                 (null (sb-kernel:layout-invalid wrapper))
                 (eq wrapper (sb-pcl::class-wrapper class)))
      (fail build 'snowgrave:unsupported-definition :graph-source-instance
            "An entry graph needs current standard-class storage; obsolete/custom storage is not updated during capture."
            :graph-capture))
    (let* ((name (graph-inspect build 'sb-mop:class-name class))
           (description (find name (build-layouts build) :key (lambda (row) (getf row :class)))))
      (unless (and description (eq class (find-class name nil))
                   (graph-inspect build 'sb-mop:class-finalized-p class))
        (fail build 'snowgrave:unsupported-definition :graph-source-instance
              "The source instance must belong to a current registered authored class." :graph-capture))
      (let* ((form (normalized-definition-form
                    build (snowgrave:find-authored-definition (build-source build) :class name)))
             (slots (graph-inspect build 'sb-mop:class-slots class)))
        (flet ((inspect-all (operation objects)
                 (mapcar (lambda (object) (graph-inspect build operation object)) objects)))
          ;; Compare actual source structure with authored/private normalized
          ;; structure. Never infer class identity from a matching name alone.
          (unless (and form
                       (equal (inspect-all 'sb-mop:class-name
                                           (graph-inspect build 'sb-mop:class-direct-superclasses class))
                              (or (third form) '(standard-object)))
                       (equal (inspect-all 'sb-mop:slot-definition-name
                                           (graph-inspect build 'sb-mop:class-direct-slots class))
                              (mapcar (lambda (slot) (if (consp slot) (car slot) slot)) (fourth form)))
                       (equal (inspect-all 'sb-mop:slot-definition-name slots) (getf description :slots))
                       (equal (inspect-all 'sb-mop:slot-definition-type slots) (getf description :slot-types))
                       (equal (remove-if-not
                               (lambda (ancestor) (member-name ancestor (build-classes build)))
                               (inspect-all 'sb-mop:class-name
                                            (graph-inspect build 'sb-mop:class-precedence-list class)))
                              (getf description :ancestors))
                       (every (lambda (slot)
                                (and (eq (class-of slot) (find-class 'sb-mop:standard-effective-slot-definition))
                                     (eq (graph-inspect build 'sb-mop:slot-definition-allocation slot) :instance)
                                     (typep (graph-inspect build 'sb-mop:slot-definition-location slot) '(integer 0)))) slots))
            (fail build 'snowgrave:unsupported-definition :graph-source-schema
                  "The original finalized class does not match its authored/private effective schema." :graph-capture)))
        (dolist (slot slots)
          (dolist (baseline *standard-graph-slot-methods*)
            (multiple-value-bind (methods certainp)
                (sb-mop:compute-applicable-methods-using-classes
                 (fdefinition (car baseline)) (list (class-of class) class (class-of slot)))
              (unless (and certainp (= (length methods) (length (cdr baseline)))
                           (every (lambda (method expected)
                                    (and (eq method (car expected))
                                         (eq (sb-mop:method-function method) (cdr expected))
                                         (let* ((source (sb-introspect:find-definition-source (cdr expected)))
                                                (path (and source (sb-introspect:definition-source-pathname source))))
                                           (and (typep path 'logical-pathname)
                                                (string= (host-namestring path) "SYS")))))
                                  methods (cdr baseline)))
                (fail build 'snowgrave:unclosed-class-operation :graph-slot-protocol
                      "A source graph slot has custom or value-sensitive read/boundness semantics." :graph-capture)))))
        (values description slots)))))

(defun capture-entry-graph (build)
  "Normalize joint EQL roots/imports after private layouts, without copying CLOS.
The existing literal pool consumes these cold node recipes for shell/fill."
  (let ((imports (getf (build-declaration build) :native-bindings))
        (entries (getf (build-declaration build) :external-domains))
        (next-id 0) (rows nil) (import-rows nil) (root-facts nil) (root-references nil))
    ;; This first profile has fixed public roots. Validate the authored
    ;; declaration before creating any internal fact; a caller cannot smuggle
    ;; :GRAPH-NODE into a mixed declaration and borrow another root's proof.
    (unless (and (snowgrave::source-finite-list-p entries)
                 (every (lambda (entry)
                          (and (snowgrave::source-finite-list-p entry) (= (length entry) 2)
                               (snowgrave::source-finite-list-p (second entry))
                               (every (lambda (domain)
                                        (and (snowgrave::source-finite-list-p domain)
                                             (= (length domain) 2) (eq (first domain) 'eql)))
                                      (second entry)))) entries))
      (fail build 'snowgrave:incomplete-domain :graph-entry-domain
            "A configuration entry needs authored EQL domains for every required argument; internal graph facts and general class entrants are not public assertions."
            :graph-capture))
    (unless (snowgrave::source-finite-list-p imports)
      (fail build 'snowgrave:unsupported-definition :graph-native-bindings
            "Native graph bindings require a finite (stable-key array) list." :graph-capture))
    (labels
        ((scalarp (value)
           (or (numberp value) (characterp value)
               (and (symbolp value) (symbol-package value))))
         (visit (value &optional import-reference import-path)
           (cond
             ((scalarp value) nil)
             ((graph-source-node build value)
              (let ((row (graph-source-node build value)))
                (when (and import-reference (null (getf row :import-reference)))
                  (fail build 'snowgrave:unsupported-definition :graph-import-order
                        "Native resource closure must precede owned graph capture." :graph-capture))
                row))
             (t
              (unless (or (consp value) (arrayp value) (graph-source-instance-p value))
                (fail build 'snowgrave:unsupported-definition :graph-node-kind
                      "An entry graph value has no finite shell/materialization ABI."
                      :graph-capture))
              (when (and import-reference (graph-source-instance-p value))
                (fail build 'snowgrave:unsupported-definition :graph-native-content
                      "An unchanged native import cannot hide a source CLOS instance." :graph-capture))
              (let ((row (list :id (prog1 next-id (incf next-id)) :source value
                               :import-reference import-reference :import-path import-path :class nil :domain nil
                               :values nil :native-links nil :literal-baseline nil
                               :slots nil :record-edge-p nil :dimensions nil :options nil
                               :backing nil :offset 0)))
                ;; Register before following any edge, so cycles close here.
                (setf (gethash value (build-graph-index build)) row)
                (push row rows)
                (cond
                  ((graph-source-instance-p value)
                   (multiple-value-bind (description slots) (validate-graph-source-instance build value)
                     (setf (getf row :class) (getf description :class)
                           (getf row :domain) (getf description :class)
                           (getf row :values)
                           (loop for slot in slots
                                 for location = (graph-inspect build 'sb-mop:slot-definition-location slot)
                                 for field = (sb-mop:standard-instance-access value location)
                                 collect (list (graph-inspect build 'sb-mop:slot-definition-name slot)
                                               (not (eq field sb-pcl::+slot-unbound+))
                                               (unless (eq field sb-pcl::+slot-unbound+) field))))
                     (dolist (field (getf row :values)) (when (second field) (visit (third field))))))
                  ((consp value)
                   (setf (getf row :domain) '(:shaped cons :external-result)
                         (getf row :values) (list (car value) (cdr value)))
                   (visit (car value) (when import-reference `(car ,import-reference))
                          (when import-path (append import-path '((:car)))))
                   (visit (cdr value) (when import-reference `(cdr ,import-reference))
                          (when import-path (append import-path '((:cdr))))))
                  (t
                   (unless (let ((type (array-element-type value)))
                             (or (member type '(t nil bit)) (native-value-type-p type)
                                 (and (consp type) (eq (car type) 'complex) (= (length type) 2)
                                      (member (second type) '(single-float double-float short-float long-float)))))
                     (fail build 'snowgrave:unsupported-definition :graph-array-element-type
                           "The entry graph array has no admitted native literal element domain." :graph-capture))
                   (unless (snowgrave::acyclic-array-displacement-p value (make-hash-table :test #'eq))
                     (fail build 'snowgrave:unsupported-definition :graph-array-displacement
                           "Native array displacement allocation must be acyclic." :graph-capture))
                   (setf (getf row :domain) (list :shaped (type-of value) :external-result)
                         (getf row :dimensions) (array-dimensions value)
                         (getf row :options) (snowgrave::array-allocation-options value :graph-backing))
                   (multiple-value-bind (parent offset) (array-displacement value)
                     (setf (getf row :backing) parent (getf row :offset) offset)
                     (let ((candidates
                             (when import-reference
                               (remove-if-not
                                (lambda (copy)
                                  (multiple-value-bind (base-parent base-offset) (array-displacement copy)
                                    (and (graph-array-geometry-matches-p copy row)
                                         (= offset base-offset)
                                         (eq parent (gethash base-parent (build-source-origins build) base-parent)))))
                                (gethash value (build-source-array-copies build))))))
                       ;; The final frozen source already owns candidate
                       ;; literal snapshots. Retain one matching the captured
                       ;; resource, if any; an unused divergent literal places
                       ;; no constraint on this configuration. Each emitted
                       ;; copy is checked against this same baseline later.
                       (if parent
                           (visit parent (when import-reference `(nth-value 0 (array-displacement ,import-reference)))
                                  (when import-path (append import-path '((:backing)))))
                           (unless (or (null (array-element-type value))
                                       (and import-reference (null candidates)
                                            (snowgrave::native-scalar-array-storage-p value)))
                             (if import-reference
                                 ;; Opaque scalar contents need admission but no
                                 ;; retained cell or generated path expression.
                                 (let ((links nil))
                                   (dotimes (index (array-total-size value))
                                     (let ((item (row-major-aref value index)))
                                       ;; Filter in place: no per-scalar
                                       ;; closure, candidate list or snapshot.
                                       (loop with previous = nil
                                             for cell = candidates then next
                                             for next = (cdr cell) while cell
                                             for expected = (row-major-aref (car cell) index)
                                             do (if (eql item (gethash expected (build-source-origins build) expected))
                                                    (setf previous cell)
                                                    (if previous (setf (cdr previous) next)
                                                        (setf candidates next))))
                                       (unless (scalarp item)
                                         (push (cons index item) links)
                                         (visit item `(row-major-aref ,import-reference ,index)
                                                (append import-path (list (list :element index)))))))
                                   (setf (getf row :native-links) (nreverse links)))
                                 (progn
                                   (setf (getf row :values)
                                         (loop for index below (array-total-size value)
                                               collect (row-major-aref value index)))
                                   (dolist (item (getf row :values)) (visit item))))))
                       (setf (getf row :literal-baseline) (car candidates))))))
                row))))
         (root-reference (value)
           (if (scalarp value) `',value
               (graph-literal-reference build value))))
      ;; Native resources close over their native backing/content aliases.
      ;; Owned nodes encountered later reuse those identities instead of clones.
      (dolist (binding imports)
        (unless (and (snowgrave::source-finite-list-p binding) (= (length binding) 2)
                     (first binding) (serializable-tree-p (first binding)) (arrayp (second binding))
                     (not (assoc (first binding) import-rows :test #'equal)))
          (fail build 'snowgrave:unsupported-definition :graph-native-bindings
                "Each native resource key is unique, stable and bound to an array." :graph-capture))
        (let* ((name (fresh-name build "NATIVE-RESOURCE"))
               (value (second binding)))
          ;; Keep process-local values in cold rows. Emitted code resolves
          ;; their stable keys from the installation's native binding context.
          (let ((row (visit value name (list :resource (first binding)))))
            (push (cons (first binding)
                        (list :name name :source value :node (getf row :id)
                              :dimensions (array-dimensions value)
                              :element-type (array-element-type value)
                              :adjustable (adjustable-array-p value)
                              :fill-pointer (when (array-has-fill-pointer-p value) (fill-pointer value)))) import-rows))))
      (dolist (entry entries)
        (let ((facts nil) (references nil))
          (dolist (domain (second entry))
            (if (and (consp domain) (eq (car domain) 'eql))
                (let ((value (second domain)))
                  (unless (scalarp value) (visit value))
                  (push (if (scalarp value) domain (graph-value-fact build value)) facts)
                  (push (root-reference value) references))
                (progn (push domain facts) (push nil references))))
          (push (cons (first entry) (nreverse facts)) root-facts)
          (push (cons (first entry) (nreverse references)) root-references)))
      (setf (build-graph-nodes build) (nreverse rows)
            (build-graph-imports build) (nreverse import-rows)
            (build-graph-root-names build) (nreverse root-facts)
            (build-graph-root-references build) (nreverse root-references))
      (dolist (row (build-graph-nodes build))
        (when (getf row :class)
          (setf (getf row :slots)
                (mapcar (lambda (field)
                          (list (first field) (second field)
                                (if (second field) (graph-value-fact build (third field)) :unknown)))
                        (getf row :values)))))
      (derive-graph-record-edges build)
      (when (build-graph-imports build)
        (let ((resource-name (fresh-name build "NATIVE-RESOURCES")))
          (setf (build-graph-resource-name build) resource-name)
          (push `(defparameter ,resource-name
                   (snowgrave::%resolve-native-bindings ',(build-identity build)
                                                       ',(graph-native-manifest build)))
                (build-generated build))
          (loop for binding in (build-graph-imports build) for index from 0
                do (push `(defparameter ,(getf (cdr binding) :name) (svref ,resource-name ,index))
                         (build-generated build)))))
      ;; Source pointers/import values remain only in cold build tables.
      (setf (getf (build-declaration build) :external-domains)
            (mapcar (lambda (entry)
                      (let ((normalized (assoc (first entry) (build-graph-root-names build) :test #'name=)))
                        (list (first entry) (copy-tree (cdr normalized))))) entries))
      (setf (getf (build-declaration build) :native-bindings)
            (mapcar #'car (build-graph-imports build)))
      build)))

(defun graph-literal-reference (build value)
  ;; Same root inventory and code recipe as ordinary native literal graphs.
  (let* ((package (build-output-package build))
         (pool (or (cdr (assoc package (build-literal-pools build)))
                   (let ((pool (make-literal-pool :name (fresh-name build "CONFIGURATION"))))
                     (push (cons package pool) (build-literal-pools build)) pool)))
         (index (or (gethash value (literal-pool-indices pool))
                    (setf (gethash value (literal-pool-indices pool))
                          (vector-push-extend value (literal-pool-values pool))))))
    `(load-time-value (svref ,(literal-pool-name pool) ,index) nil)))

(defun entry-graph-request-p (build)
  (or (getf (build-declaration build) :native-bindings)
      (some (lambda (entry)
              (some (lambda (domain)
                      (and (consp domain) (eq (car domain) 'eql)
                           (let ((value (second domain)))
                             (or (consp value) (arrayp value) (graph-source-instance-p value)))))
                    (second entry)))
            (getf (build-declaration build) :external-domains))))

(defun graph-native-manifest (build)
  "Serializable native identity/geometry obligations; no source values/code."
  (list :resources
        (mapcar (lambda (binding) (list :key (car binding) :node (getf (cdr binding) :node)))
                (build-graph-imports build))
        :nodes
        (loop for row in (build-graph-nodes build) when (getf row :import-path)
              collect
              (let ((options (getf row :options)))
                (append (list :id (getf row :id) :path (getf row :import-path)
                              :kind (if (consp (getf row :source)) :cons :array)
                              :links (if (arrayp (getf row :source))
                                         (loop for (index . value) in (getf row :native-links)
                                               collect (list index (getf (graph-source-node build value) :id)))
                                         (loop for value in (getf row :values) for index from 0
                                               for target = (graph-source-node build value)
                                               when target
                                                 collect (list (if (zerop index) :car :cdr)
                                                               (getf target :id)))))
                        (when options
                          (list :dimensions (getf row :dimensions)
                                :element-type (getf options :element-type)
                                :adjustable (getf options :adjustable)
                                :has-fill-pointer (not (null (member :fill-pointer options)))
                                :fill-pointer (getf options :fill-pointer)
                                :backing (let ((parent (getf row :backing)))
                                           (when parent (getf (graph-source-node build parent) :id)))
                                :offset (getf row :offset))))))))

;;;; State preservation and private-record boundary.

(defun graph-node-domain-p (domain)
  ;; Exact captured identity, not a class assertion or a public CL type.
  (and (consp domain) (eq (car domain) :graph-node)
       (snowgrave::source-finite-list-p domain) (= (length domain) 3)
       (typep (second domain) '(integer 0 *))))

(defun owned-record-domain-p (domain)
  ;; A normal-return allocation family, never a singleton identity or EQL key.
  (and (consp domain) (eq (first domain) :owned-record)
       (snowgrave::source-finite-list-p domain) (= (length domain) 2)
       (symbolp (second domain))))

(defun private-record-domain-base (domain)
  (cond ((relational-value-domain-p domain) (private-record-domain-base (third domain)))
        ((initializing-record-domain-p domain) (third domain))
        ((graph-node-domain-p domain) (third domain))
        ((owned-record-domain-p domain) (second domain))
        ((and (consp domain) (eq (first domain) 'or))
         (cons 'or (mapcar #'private-record-domain-base (rest domain))))
        (t domain)))

(defun owned-record-layout (build domain)
  (when (owned-record-domain-p domain)
    (find (second domain) (build-layouts build) :key (lambda (row) (getf row :class)) :test #'name=)))

(defun graph-node-row (build domain)
  (when (graph-node-domain-p domain)
    (find (second domain) (build-graph-nodes build) :key (lambda (row) (getf row :id)) :test #'eql)))

(defun graph-state-profile-p (build) (not (null (build-graph-nodes build))))

(defun derive-graph-record-edges (build)
  "Close private payload reachability over the existing cold node inventory."
  (let ((parents (make-hash-table :test #'eq)) (pending nil))
    (labels ((edge (parent value)
               (let ((child (graph-source-node build value)))
                 (when child (push parent (gethash child parents))))))
      (dolist (row (build-graph-nodes build))
        (setf (getf row :record-edge-p) (not (null (getf row :class))))
        (if (getf row :class)
            (push row pending)
            (progn
              (dolist (value (if (and (getf row :import-reference) (arrayp (getf row :source)))
                                (mapcar #'cdr (getf row :native-links))
                                (getf row :values)))
                (edge row value))
              (when (getf row :backing) (edge row (getf row :backing))))))
      (loop while pending for child = (pop pending) do
        (dolist (parent (gethash child parents))
          (unless (getf parent :record-edge-p)
            (setf (getf parent :record-edge-p) t)
            (push parent pending))))))
  build)

(defun graph-private-containers-p (build)
  (some (lambda (row) (and (not (getf row :class)) (getf row :record-edge-p)))
        (build-graph-nodes build)))

(defun graph-private-container-domain-p (build domain)
  ;; Shape cannot establish payload custody. Exact captured identities carry
  ;; the cold closure proof; a lost/opaque identity is conservative whenever
  ;; this installation can contain a private native aggregate. Source stores
  ;; and aggregate construction cannot introduce further private edges.
  (some (lambda (part)
          (cond ((relational-value-domain-p part)
                 (graph-private-container-domain-p build (third part)))
                ((graph-node-domain-p part)
                 (let ((row (graph-node-row build part)))
                   (or (null row)
                       (and (not (getf row :class))
                            (multiple-value-bind (key value) (get-properties row '(:record-edge-p))
                              (or (null key) value))))))
                ((record-domain-p build part) nil)
                ;; A qualified function target cannot be a cons/array, even
                ;; when this installation also owns a private container.
                ((domain-function-target part) nil)
                ((native-data-type-p build (value-domain-shape build part)) nil)
                (t (graph-private-containers-p build))))
        (domain-alternatives domain)))

(defun graph-captured-identity-domain-p (build domain)
  ;; Joint capture/materialization preserves identity and distinctness for
  ;; these exact unit values. This does not license recursive native EQUALP.
  (every (lambda (part)
           (if (relational-value-domain-p part)
               (graph-captured-identity-domain-p build (third part))
               (and (graph-node-domain-p part) (graph-node-row build part))))
         (domain-alternatives domain)))

(defun graph-private-callable-domain-p (build domain)
  ;; A condition can publish a relocated callable just as it can publish a
  ;; private record. Exact non-cohort targets keep their unchanged native
  ;; binding; a nominal FUNCTION fact alone establishes no such identity.
  (some (lambda (part)
          (cond ((relational-value-domain-p part)
                 (graph-private-callable-domain-p build (third part)))
                ((graph-node-domain-p part)
                 (graph-private-callable-domain-p build (third part)))
                ((external-value-domain-p build part) nil)
                ((domain-function-target part)
                 (let ((name (domain-function-target part)))
                   (or (member-name name (build-functions build))
                       (member-name name (getf (build-declaration build) :closed-generics)))))
                ((member part '(:unknown :pending :external-result)) t)
                (t (or (subtype-domain-p build part 'function)
                       (subtype-domain-p build 'function part)))))
        (domain-alternatives domain)))

(defun graph-private-payload-domain-p (build domain)
  (or (graph-private-record-domain-p build domain)
      (graph-private-container-domain-p build domain)
      (graph-private-callable-domain-p build domain)))

(defun lowered-callable-target-p (build domain)
  (let ((name (domain-function-target domain)))
    (and name (or (member-name name (build-functions build))
                  (member-name name (getf (build-declaration build) :closed-generics))))))

(defun lowered-type-input-p (build domain type)
  "Whether a checked native type could observe a changed representation."
  (cond ((relational-value-domain-p domain) (lowered-type-input-p build (third domain) type))
        ((and (consp domain) (eq (first domain) 'or))
         (some (lambda (part) (lowered-type-input-p build part type)) (rest domain)))
        ((graph-node-domain-p domain)
         (let ((row (graph-node-row build domain)))
           (or (null row) (getf row :class)
               (getf row :record-edge-p))))
        ((or (owned-record-domain-p domain) (initializing-record-domain-p domain)
             (record-domain-p build domain) (lowered-callable-target-p build domain)) t)
        ;; These targets retain their actual native identity. A surrounding
        ;; cohort does not change their type or their error payload.
        ((or (domain-function-target domain) (external-value-domain-p build domain)) nil)
        ((and (graph-state-profile-p build) (graph-private-payload-domain-p build domain)) t)
        ;; Nominal supertypes and forgotten facts can still carry a lowered
        ;; class or source function. Do not grant them the native CLOS ABI.
        (t
         ;; Outside a private installation, an unknown ordinary native
         ;; operand may legitimately fail its check. Only a source-accepted
         ;; lowered alternative can turn that native success into failure.
         (let ((unknownp (member domain '(:unknown :pending :external-result))))
           (or (some (lambda (class)
                       (and (or unknownp (subtype-domain-p build class domain))
                            (subtype-domain-p build class type)))
                     (build-classes build))
               (some (lambda (name)
                       (let ((target (list :function-target name)))
                         (and (or unknownp (subtype-domain-p build target domain))
                              (subtype-domain-p build target type))))
                     (append (build-functions build)
                             (getf (build-declaration build) :closed-generics))))))))

(defun physical-type-acceptance-p (build domain type)
  "Prove acceptance of the lowered value, independently of its source type.
CLOSED-RECORD is the actual runtime ABI. Relocated functions use FUNCTION as
an intentionally conservative physical supertype; source generic-function
classification remains the separate logical subtype owner's responsibility."
  (labels ((accepts (physical)
             (multiple-value-bind (yes certainp) (subtypep physical type)
               (and yes certainp)))
           (walk (fact)
             (cond ((relational-value-domain-p fact) (walk (third fact)))
                   ((and (consp fact) (eq (first fact) 'or)) (every #'walk (rest fact)))
                   ((graph-node-domain-p fact)
                    (let ((row (graph-node-row build fact)))
                      (if (and row (not (getf row :class)))
                          (walk (third fact))
                          (accepts 'snowgrave::closed-record))))
                   ((or (owned-record-domain-p fact) (initializing-record-domain-p fact)
                        (record-domain-p build fact))
                    (accepts 'snowgrave::closed-record))
                   ((domain-function-target fact)
                    (if (lowered-callable-target-p build fact)
                        (accepts 'function)
                        ;; The same native function reaches the host check.
                        (subtype-domain-p build fact type)))
                   ((shaped-domain-p fact) (accepts (second fact)))
                   ((external-value-domain-p build fact) t)
                   ((member fact '(:unknown :pending :external-result)) (accepts t))
                   (t
                    (and (subtype-domain-p build fact type)
                         (or (not (some (lambda (class) (subtype-domain-p build class fact))
                                        (build-classes build)))
                             (accepts 'snowgrave::closed-record))
                         (or (not (some (lambda (name)
                                          (subtype-domain-p build (list :function-target name) fact))
                                        (append (build-functions build)
                                                (getf (build-declaration build) :closed-generics))))
                             (accepts 'function)))))))
    (walk domain)))

(defun audit-private-type-input (build type domain feature)
  ;; Native checks retain their actual operand in TYPE-ERROR. Source TYPEP
  ;; semantics cannot prove acceptance of a record/function representation.
  (when (and (not *collect-function-flow*) (lowered-type-input-p build domain type)
             (not (and (subtype-domain-p build domain type)
                       (physical-type-acceptance-p build domain type))))
    (fail build 'snowgrave:unclosed-class-operation feature
          "A checked type needs both source and physical acceptance for a lowered or private datum."
          :reachability)))

(defun audit-declaration-payloads (build declarations)
  (unless *collect-function-flow*
    (dolist (declaration declarations)
      (when (and (consp declaration)
                 (not (member (first declaration)
                              '(special dynamic-extent ignore ignorable inline notinline ftype optimize declaration))))
        (let* ((explicitp (eq (first declaration) 'type))
               (type (if explicitp (second declaration) (first declaration)))
               (names (if explicitp (cddr declaration) (cdr declaration))))
          (dolist (name names)
            (when (symbolp name)
              (audit-private-type-input build type (binding-value-domain name)
                                        :private-type-declaration-error))))))))

(defun prepare-graph-state-proof (build)
  ;; Inventory the complete source obligation before caller inference. Finite
  ;; captured fields may close inductively; unresolved writes retain the old
  ;; conservative invalidation. Mutable scalars are never snapshot constants.
  (audit-graph-state-entry-profile build)
  ;; Captured native containers may retain private records. Their transitive
  ;; payload proof is consumed at observable operations, not a global ban on
  ;; retaining an otherwise unused container in the private installation.
  (clrhash (build-graph-field-writes build))
  (let ((writes nil) (unbinds nil) (forced-writes nil) (forced-unbinds nil))
    (labels ((invalidate (slot-form &optional unbindp site)
               (multiple-value-bind (slot literalp) (quoted-value slot-form)
                 (if literalp
                     (progn
                       (pushnew slot writes)
                       (when unbindp (pushnew slot unbinds))
                       (if site (register-graph-field-write build site slot unbindp)
                           (progn (pushnew slot forced-writes)
                                  (when unbindp (pushnew slot forced-unbinds)))))
                     ;; A dynamic name has no finite effective-slot owner.
                     ;; Final source admission still applies its own refusal.
                     (dolist (layout (build-layouts build))
                       (dolist (name (getf layout :slots))
                         (pushnew name writes) (pushnew name forced-writes)
                         (when unbindp (pushnew name unbinds) (pushnew name forced-unbinds)))))))
             (place (form &optional enclosingp)
               (when (consp form)
                 (case (first form)
                   (slot-value
                    ;; GETF can replace its containing generalized place.
                    ;; There is no direct slot-store receipt for that write.
                    (invalidate (third form) nil (unless enclosingp form)))
                   (getf (place (second form) t))
                   (the (place (third form) t))
                   (values (dolist (part (rest form)) (place part t))))))
             (walk (form)
               (when (and (consp form) (not (eq (car form) 'quote)))
                 ;; Source reinitialization, including a saved/indirect
                 ;; initialization callable, can replace existing field edges.
                 ;; Compiler-owned stock delegation is not an authored call.
                 (when (or (initialization-generic-p (first form))
                           (and (eq (first form) 'function)
                                (initialization-generic-p (second form))))
                   (dolist (layout (build-layouts build))
                     (dolist (slot (getf layout :slots)) (pushnew slot writes) (pushnew slot forced-writes))))
                 (case (car form)
                   (setf (loop for tail on (cdr form) by #'cddr do (place (first tail))))
                   ((incf decf pop) (place (second form)))
                   ((push pushnew) (place (third form)))
                   (slot-makunbound (invalidate (third form) t form))
                   ((snowgrave::%record-write snowgrave::%record-unbind)
                    (invalidate (third form) (eq (car form) 'snowgrave::%record-unbind))))
                 (mapc #'walk form))))
      (dolist (form (build-forms build))
        (with-build-source-key (build (authored-source-key build form))
        ;; A selected generated writer remains a root even without an early
        ;; caller. Its write cannot be omitted from the state obligation.
        (when (eq (defining-kind form) :class)
          (dolist (slot (fourth form))
            (when (consp slot)
              (loop for (option name) on (cdr slot) by #'cddr
                    when (and (member option '(:writer :accessor))
                              (member-name (if (eq option :accessor) (list 'setf name) name)
                                           (getf (build-declaration build) :closed-generics)))
                    do (pushnew (first slot) writes) (pushnew (first slot) forced-writes)))))
        (walk form))))
    (setf (build-graph-state-invalidations build)
          (list :writes writes :unbinds unbinds :forced-writes forced-writes :forced-unbinds forced-unbinds))
    (initialize-graph-field-envelopes build)))

(defun private-record-slot-row (build domain)
  (when (relational-value-domain-p domain)
    (return-from private-record-slot-row (private-record-slot-row build (third domain))))
  (cond ((initializing-record-domain-p domain)
         (or (initialization-record-row domain) (original-record-flow-row build domain)
             (unchanged-record-flow-row build domain)))
        ((graph-node-domain-p domain) (graph-node-row build domain))
        ((owned-record-domain-p domain)
         (let ((layout (owned-record-layout build domain)))
           (when (getf layout :construction-state)
             (list :class (getf layout :class) :slots (getf layout :construction-state)))))))

(defun record-slot-entry-fact (build domain slot)
  ;; The field fact owner serves direct reads, generated readers and helper
  ;; entry projection. Origin invalidation is identical for all three.
  (let* ((row (private-record-slot-row build domain))
         (field (assoc slot (getf row :slots)))
         (unchanged (unless (or (and field (eq (second field) :pending))
                               (member slot (getf (build-graph-state-invalidations build) :writes)))
                      (assoc slot (getf (unchanged-record-flow-row build domain) :slots))))
         (currentp (and (initialization-domain-current-p domain)
                        (initialization-record-row domain))))
    (when unchanged
      (return-from record-slot-entry-fact (values (second unchanged) (third unchanged) t (fourth unchanged))))
    (when (and (getf row :class) field)
      (let* ((prior (third field))
             (invalidations (build-graph-state-invalidations build))
             (envelope (unless currentp (graph-field-envelope build domain slot)))
             (status (if envelope (first envelope)
                         (if (and (not currentp) (member slot (getf invalidations :unbinds))) nil (second field))))
             (value (if envelope (second envelope)
                        (if (and (not currentp) (member slot (getf invalidations :writes)))
                        (merge-value-domains build (if (external-value-observation-p build prior)
                                                      :external-result prior) :unknown)
                        prior))))
        (values status value t (when currentp (fourth field)))))))

(defun graph-record-slot-facts (build receiver slot)
  "Use the same read owner for exact captures and joined fresh-family facts."
  (let ((alternatives (domain-alternatives (relational-base receiver))) (value :pending))
    (when alternatives
      (dolist (domain alternatives (values t value))
        (multiple-value-bind (status current presentp) (record-slot-entry-fact build domain slot)
          (when (eq status :pending) (return (values nil :pending)))
          (unless (and presentp (eq status t)) (return (values nil :unknown)))
          (setf value (merge-value-domains build value current)))))))

(defun record-slot-read-domain (build receiver-form slot-form)
  ;; Authored reads and MOP-generated readers use this one fact owner. A class
  ;; or declared slot type alone proves neither boundness nor restart result.
  (multiple-value-bind (slot literalp) (quoted-value slot-form)
    (if literalp
        (multiple-value-bind (boundp domain) (graph-record-slot-facts build (value-domain build receiver-form) slot)
          (values (if (or boundp (eq domain :pending)) domain :unknown) boundp))
        (values :unknown nil))))

(defun audit-graph-state-entry-profile (build)
  (dolist (entry (getf (build-declaration build) :entries))
    (let* ((form (ordinary-function-form build entry))
           (contract (lambda-contract build (third form)))
           (roots (assoc entry (build-graph-root-names build) :test #'name=))
           (references (assoc entry (build-graph-root-references build) :test #'name=)))
      (with-build-source-key (build (authored-source-key build form))
        (unless (and roots references (= (length (cdr roots)) (length (getf contract :required)))
                     (= (length (cdr references)) (length (cdr roots))) (every #'identity (cdr references))
                     (every (lambda (domain)
                              (or (and (graph-node-domain-p domain) (graph-node-row build domain))
                                  (and (consp domain) (eq (first domain) 'eql)))) (cdr roots))
                     (not (getf contract :optional)) (not (getf contract :rest)) (not (getf contract :keyp)))
          (fail build 'snowgrave:incomplete-domain :graph-state-entry-domain
                "This state profile requires a fixed EQL configuration for every public required argument and no optional/rest/key caller inputs."
                :reachability))))))

(defun graph-private-record-domain-p (build domain)
  ;; This is an overlap test over the existing class-domain owner, not a
  ;; reachability exemption. Every selected disjoint class cell retains its
  ;; ordinary slot/error semantics. A broad base class can still hold a
  ;; captured subclass and therefore cannot borrow this disjointness proof.
  (some (lambda (part)
          ;; The opaque envelope also covers clean alternatives joined with
          ;; native returns. One such alternative may be a private record.
          (cond ((relational-value-domain-p part)
                 (graph-private-record-domain-p build (third part)))
                ((member part '(:pending :unknown :external-result)) t)
                ((owned-record-domain-p part) t)
                ((initializing-record-domain-p part)
                 ;; A relational formal adds identity to an ordinary caller
                 ;; view; it does not turn a disjoint nominal selected cell
                 ;; into a private allocation. Actual initializer shells have
                 ;; no such origin and always retain private custody.
                 (let ((origin (find (second part) *flow-record-origins* :key #'second :test #'eq)))
                   (if origin
                       (or (fifth origin) (graph-private-record-domain-p build (fourth origin)))
                       t)))
                ((graph-node-domain-p part)
                 (let ((row (graph-node-row build part)))
                   (or (null row) (not (null (getf row :class))))))
                (t (some (lambda (row)
                           (let ((class (getf row :class)))
                             (and class (subtype-domain-p build class part))))
                         (append (build-graph-nodes build)
                                 (remove-if-not (lambda (row) (getf row :construction-reached-p))
                                                (build-layouts build)))))))
        (domain-alternatives domain)))

(defun private-record-slot-present-p (build domain slot)
  ;; Presence is a class/layout property even for a joined formal state row.
  ;; The row's union of keys cannot invent a slot on another alternative.
  (let* ((base (private-record-domain-base domain))
         (layouts (remove-if-not (lambda (layout) (subtype-domain-p build (getf layout :class) base))
                                 (build-layouts build))))
    (and layouts (every (lambda (layout) (member slot (getf layout :slots))) layouts))))

(defun audit-graph-record-slot (build receiver-form slot-form &key bound)
  (when (and (graph-state-profile-p build) (not *collect-function-flow*)
             (graph-private-record-domain-p build (value-domain build receiver-form)))
    (multiple-value-bind (slot literalp) (quoted-value slot-form)
      (let ((alternatives (domain-alternatives (value-domain build receiver-form))))
        (unless (and literalp alternatives
                     (if bound
                         (nth-value 0 (graph-record-slot-facts build (value-domain build receiver-form) slot))
                         (every (lambda (domain) (private-record-slot-present-p build domain slot)) alternatives)))
          (fail build 'snowgrave:unclosed-class-operation :graph-state-slot-read
                "A private state record needs an exact existing slot and preserved boundness before an operation could expose it in a slot condition."
                :reachability))))))

(defun audit-graph-native-inputs (build arguments feature)
  (unless (every (lambda (argument) (native-data-form-p build argument)) arguments)
    (fail build 'snowgrave:unclosed-call feature
          "This state profile needs native data at an observable boundary; private records, dependent callables and unproved aggregate contents cannot escape."
          :reachability)))

(defun audit-graph-ordinary-inputs (build name arguments)
  ;; A bounded state-effect profile over the existing operation owners, not a
  ;; second dispatcher. Operations lacking a data/error exposure proof refuse.
  (when (and (graph-state-profile-p build) (not *collect-function-flow*))
    (cond
      ((eq name 'snowgrave::%record-read)
       (audit-graph-record-slot build (first arguments) (second arguments) :bound t))
      ((eq name 'snowgrave::%record-write)
       (audit-graph-record-slot build (first arguments) (second arguments))
       (audit-stored-record-value build (first arguments) (second arguments) (value-domain build (third arguments))))
      ((member name *ordinary-operations*)
       (let ((count (length arguments)))
         (unless (or (eq name 'values)
                     ;; LIST* with one argument is identity. Actual aggregate
                     ;; construction needs native-data operands below, so a
                     ;; private record cannot hide in a later condition object.
                     (and (eq name 'list*) (= count 1))
                     (and (= count 1)
                          (member name '(identity not null atom consp symbolp numberp integerp rationalp
                                         floatp realp complexp stringp characterp vectorp arrayp keywordp)))
                     (and (= count 2) (member name '(eq eql equal equalp))
                          (not (and (eq name 'equalp)
                                    (some (lambda (argument)
                                            (graph-private-container-domain-p build (value-domain build argument)))
                                          arguments)))))
           (let ((receiver (native-sequence-argument-position name)))
             (loop for argument in arguments for position from 0
                   unless (and receiver (= position receiver) (native-sequence-form-p build argument)
                               (not (graph-private-container-domain-p build (value-domain build argument))))
                   do (audit-graph-native-inputs build (list argument) :graph-state-operation-input)))))))))

(defun audit-graph-entry-result (build name)
  (when (graph-state-profile-p build)
    (let ((summary (gethash name (build-function-returns build))))
      (unless (and (return-summary-p summary) (return-summary-completep summary)
                   (every (lambda (domain) (native-data-domain-p build domain)) (return-summary-domains summary)))
        (fail build 'snowgrave:unclosed-call :graph-state-result
              "Every public state entry must keep private records and dependent aggregates/callables behind its native result boundary."
              :reachability)))))

(defun graph-native-payload-form-p (build form)
  ;; Reuse the mutable-binding fixed point, not a fresh value/shape assertion.
  ;; CONS preserves its operands; successful CAR/CDR only select old payload.
  (cond ((and (symbolp form) (assoc form *function-bindings*))
         (or (binding-native-payload-p form)
             (not (graph-private-payload-domain-p build (value-domain build form)))))
        ((and (consp form) (member (first form) '(cons car cdr)))
         (every (lambda (argument) (graph-native-payload-form-p build argument)) (rest form)))
        (t (not (graph-private-payload-domain-p build (value-domain build form))))))

(defun audit-graph-update-payload (build domain &optional nativep)
  ;; Host read/modify/write macros can fail before their writer runs. Their
  ;; old value, numeric delta, new item or list tail can become a condition
  ;; datum or an aggregate edge. The successful writer's value is no proof
  ;; about these distinct inputs. Unchanged native callable bindings retain
  ;; their actual identity; relocated/opaque payloads need an explicit ABI.
  (when (and (graph-state-profile-p build) (not *collect-function-flow*)
             (not nativep) (graph-private-payload-domain-p build domain))
    (fail build 'snowgrave:unclosed-call :graph-state-update-input
          "A native place update needs a data/error proof for its old value and operands." :reachability)))


;;;; Construction shares finalized layout, source, lambda and return owners.

(defun construction-protocol (build class)
  (let ((layout (find class (build-layouts build) :key (lambda (row) (getf row :class)) :test #'name=)))
    (or (getf layout :construction-protocol)
        (let ((host (find-class (mapped-name class (build-open-package build)))))
          (verify-standard-construction build host)
          (multiple-value-bind (legal allow) (construction-initarg-contract build host)
            (setf (getf layout :construction-protocol)
                  (list :legal legal :allow allow
                        :stock (every (lambda (operation)
                                        (every (lambda (method)
                                                 (eq method (second (assoc operation *standard-initialization-methods*))))
                                               (initialization-methods build operation host)))
                                      '(initialize-instance shared-initialize)))))))))

(defun call-in-initializer-environment (build initializer process)
  (let ((*argument-domains* nil) (*function-bindings* nil)
        (*local-function-frames* nil) (*value-domain-local-functions* nil)
        (*mutable-invariant-bindings* nil) (*declared-specials* nil)
        (*current-method* nil) (*effective-return-proof* nil) (*fixed-effective-arguments* nil)
        (*initialization-phase* nil) (*initialization-next* nil) (*initialization-plan* nil)
        (*flow-record-origins* nil) (*flow-value-receipts* nil)
        (*immediate-callee-value* nil) (*generated-class-operation* nil)
        (*tagbody-targets* nil) (*immediate-lambda-domains* nil))
    (with-build-source-key (build (getf initializer :source-key)) (funcall process))))

(defun construction-initializer-domain (build initializer)
  (call-in-initializer-environment build initializer
    (lambda () (value-domain build (getf initializer :form)))))

(defun audit-record-slot-value-domain (build layout slot domain &optional (feature :construction-private-type-error))
  ;; SG-RECORD-WRITE's TYPE-ERROR retains VALUE, not just a nominal type.
  ;; A private record/container or relocated callable therefore needs actual
  ;; acceptance proof; a source callable's native fcell is not its emitted one.
  (when (and (graph-state-profile-p build) (not *collect-function-flow*))
    (let* ((index (position slot (getf layout :slots)))
           (type (nth index (getf layout :slot-types))))
      (when (and (external-result-domain-p domain)
                 (snowgrave::class-reference-slot-type-p type (build-classes build)))
        (fail build 'snowgrave:unclosed-call :external-result-state
              "An opaque native initarg has no closed class-reference slot ABI." :reachability))
      (when (and (graph-private-payload-domain-p build domain)
                 (not (subtype-domain-p build domain type)))
        (fail build 'snowgrave:unclosed-class-operation feature
              "A private or relocated datum needs proved slot-type acceptance before an error could publish it."
              :reachability)))))

(defun audit-construction-slot-domain (build layout slot domain)
  (audit-record-slot-value-domain build layout slot domain))

(defun audit-stored-record-value (build receiver slot-form domain)
  (when (and (graph-state-profile-p build) (not *collect-function-flow*))
    (multiple-value-bind (slot literalp) (quoted-value slot-form)
      (unless literalp
        (fail build 'snowgrave:unclosed-class-operation :dynamic-slot
              "A stored record field needs its constant slot owner." :reachability))
      (dolist (layout (validate-record-slot build receiver slot))
        (unless (member slot (getf layout :slots))
          (fail build 'snowgrave:unclosed-class-operation :graph-state-slot-read
                "A stored field must exist on every possible private receiver." :reachability))
        (audit-record-slot-value-domain build layout slot domain :graph-state-write)))))

(defun audit-construction-initarg-domain (build layout key domain)
  (when (and (graph-state-profile-p build) (not *collect-function-flow*))
    (let ((targets (loop for slot in (getf layout :slots) for names in (getf layout :slot-initargs)
                         when (member key names) collect slot)))
      (when (and (graph-private-payload-domain-p build domain) (null targets))
        (fail build 'snowgrave:unclosed-class-operation :construction-private-initarg
              "A potentially private initarg needs an accepted slot owner; an ignored key or custom keyword cannot borrow one."
              :reachability))
      (dolist (slot targets) (audit-construction-slot-domain build layout slot domain)))))

(defun source-construction-domain (build form)
  (multiple-value-bind (class literalp) (quoted-value (second form))
    (unless (and literalp (member-name class (build-classes build)))
      (return-from source-construction-domain :unknown))
    (unless (graph-state-profile-p build) (return-from source-construction-domain class))
    (let* ((layout (find class (build-layouts build) :key (lambda (row) (getf row :class)) :test #'name=))
           (protocol (construction-protocol build class))
           (arguments (cddr form)) (plist nil)
           (recursivep (member class *active-construction-classes* :test #'name=))
           (*active-construction-classes* (cons class *active-construction-classes*)))
      (unless (and (evenp (length arguments))
                   (loop for tail on arguments by #'cddr always (keywordp (first tail))))
        (return-from source-construction-domain :unknown))
      (loop for (key value) on arguments by #'cddr
            for domain = (value-domain build value)
            do (when (active-initialization-shell-p domain)
                 (fail build 'snowgrave:unclosed-class-operation :initialization-activation-escape
                       "A constructor cannot retain an enclosing symbolic initialization receiver without activation transport." :reachability))
               (audit-construction-initarg-domain build layout key domain)
               (setf plist (append plist (list key (persistent-record-flow-domain domain)))))
      ;; GET-PROPERTIES below mirrors the materializer's first-occurrence
      ;; selection across all accepted names. Every initializer is still
      ;; emitted/audited by its original owner, including omitted profiles.
      (dolist (default (getf layout :default-initargs))
        (unless (nth-value 2 (get-properties plist (list (first default))))
          (let* ((initializer (list :form (second default) :source-key (getf (cddr default) :source-key)))
                 (domain (if recursivep :pending (construction-initializer-domain build initializer))))
            (audit-construction-initarg-domain build layout (first default) domain)
            (setf plist (append plist (list (first default) domain))))))
      (when (and (not *collect-function-flow*)
                 (loop for tail on plist by #'cddr
                       thereis (graph-private-payload-domain-p build (second tail)))
                 (not (getf protocol :allow))
                 (not (let ((allow (getf plist :allow-other-keys '(eql nil))))
                        (subtype-domain-p build allow '(not null))))
                 (loop for tail on plist by #'cddr
                       thereis (not (or (eq (first tail) :allow-other-keys)
                                        (member (first tail) (getf protocol :legal))))))
        (fail build 'snowgrave:unclosed-class-operation :construction-private-keywords
              "A constructor carrying private initargs needs proved keyword acceptance before any validation/error path."
              :reachability))
      (let ((state
              (loop for slot in (getf layout :slots) for names in (getf layout :slot-initargs)
                    for initializer in (getf layout :slot-initforms)
                    collect (multiple-value-bind (key value tail) (get-properties plist names)
                              (declare (ignore key))
                              (let* ((boundp (and (getf protocol :stock) (or tail initializer)))
                                     (domain (cond (tail value)
                                                   (initializer (if recursivep :pending (construction-initializer-domain build initializer)))
                                                   (t :unknown))))
                                (when (or tail initializer) (audit-construction-slot-domain build layout slot domain))
                                (list slot (not (null boundp)) (if boundp domain :unknown)))))))
        (cond (*collect-function-flow*
               (let* ((reachedp (getf layout :construction-reached-p))
                      (old (getf layout :construction-state))
                      (joined (if reachedp
                                  (mapcar (lambda (before after)
                                            (list (first before) (and (second before) (second after))
                                                  (merge-value-domains build (third before) (third after)))) old state)
                                  state)))
                 (unless (and reachedp (equal old joined))
                   (setf (getf layout :construction-reached-p) t (getf layout :construction-state) joined
                         *function-flow-changed* t))))
              ((not (getf layout :construction-reached-p))
               (fail build 'snowgrave:incomplete-domain :construction-reachability
                     "A source constructor lacks its joined normal-return family proof." :reachability))))
      (list :owned-record class))))

(defun audit-initialization-state-inputs (build name arguments)
  (when (and (graph-state-profile-p build) (not *collect-function-flow*))
    (let* ((required (if (eq name 'shared-initialize) 2 1))
           (receiver (value-domain build (first arguments))))
      (dolist (part (domain-alternatives receiver))
        (let* ((class (private-record-domain-base part))
               (layout (find class (build-layouts build) :key (lambda (row) (getf row :class)) :test #'name=)))
          (unless layout
            (fail build 'snowgrave:unclosed-class-operation :initialization-state-receiver
                  "Private initialization needs an admitted record layout." :reachability))
          (loop for (key value) on (nthcdr required arguments) by #'cddr
                do (audit-construction-initarg-domain build layout key (value-domain build value))))))))

(defun settle-construction-domains (build)
  ;; Same quiescent outer fixedpoint, after all selected roots have had their
  ;; replay. No unknown tail or fictitious successful value count is invented.
  (when (and *settled-method-roots* (not *function-flow-changed*))
    (dolist (layout (build-layouts build))
      (dolist (field (getf layout :construction-state))
        (when (eq (third field) :pending)
          (setf (third field) :unknown *function-flow-changed* t))))))
