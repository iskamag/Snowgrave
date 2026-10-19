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
               (if (graph-source-node build expected)
                   (eq (graph-literal-origin build copy) expected)
                   (eql copy expected))))
        (unless
            (cond
              ((consp origin)
               (and (consp value)
                    (same-edge (car value) (first (getf row :values)))
                    (same-edge (cdr value) (second (getf row :values)))))
              ((arrayp origin)
               (and (arrayp value)
                    (equal (array-dimensions value) (getf row :dimensions))
                    (let ((options (getf row :options)))
                      (and (equal (array-element-type value) (getf options :element-type))
                           (eq (not (null (adjustable-array-p value))) (getf options :adjustable))
                           (eq (not (null (array-has-fill-pointer-p value)))
                               (not (null (member :fill-pointer options))))
                           (or (not (array-has-fill-pointer-p value))
                               (eql (fill-pointer value) (getf options :fill-pointer)))))
                    (multiple-value-bind (parent offset) (array-displacement value)
                      (and (= offset (getf row :offset))
                           (if (getf row :backing)
                               (and parent (same-edge parent (getf row :backing)))
                               (and (null parent)
                                    (or (null (array-element-type value))
                                        (loop for element in (getf row :values) for index from 0
                                              always (same-edge (row-major-aref value index) element)))))))))
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
                               :values nil :slots nil :record-edge-p nil :dimensions nil :options nil
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
                     (if parent
                         (visit parent (when import-reference `(nth-value 0 (array-displacement ,import-reference)))
                                (when import-path (append import-path '((:backing)))))
                         (unless (null (array-element-type value))
                           (setf (getf row :values)
                                 (loop for index below (array-total-size value)
                                       collect (row-major-aref value index)))
                           (loop for item in (getf row :values) for index from 0
                                 do (visit item (when import-reference `(row-major-aref ,import-reference ,index))
                                           (when import-path (append import-path (list (list :element index)))))))))))
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
        (if (getf row :class)
            (setf (getf row :slots)
                  (mapcar (lambda (field)
                            (list (first field) (second field)
                                  (if (second field) (graph-value-fact build (third field)) :unknown)))
                          (getf row :values)))
            (setf (getf row :record-edge-p)
                  (some (lambda (value)
                          (let ((child (graph-source-node build value)))
                            (and child (getf child :class) t)))
                        (getf row :values)))))
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
                              :links (loop for value in (getf row :values) for index from 0
                                           for target = (graph-source-node build value)
                                           when target
                                             collect (list (if (consp (getf row :source))
                                                               (if (zerop index) :car :cdr) index)
                                                           (getf target :id))))
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

(defun graph-node-domain (domain)
  (if (graph-node-domain-p domain) (third domain) domain))

(defun graph-node-row (build domain)
  (when (graph-node-domain-p domain)
    (find (second domain) (build-graph-nodes build) :key (lambda (row) (getf row :id)) :test #'eql)))

(defun graph-state-profile-p (build) (not (null (build-graph-nodes build))))

(defun prepare-graph-state-proof (build)
  ;; Conservative complete-source preservation, independent of reachability
  ;; guesses. A write invalidates captured value facts; an unbind additionally
  ;; invalidates boundness. Mutable scalar fields are never snapshot constants.
  (audit-graph-state-entry-profile build)
  ;; Native sequence conditions can retain their receiver. The first state
  ;; profile therefore admits no container edge into the private record graph.
  ;; This marker is derived by the existing cold edge inventory, never supplied
  ;; as an assertion by the caller. Missing evidence is not a false marker.
  (dolist (row (build-graph-nodes build))
    (unless (getf row :class)
      (multiple-value-bind (key record-edge-p) (get-properties row '(:record-edge-p))
        (unless (and key (not record-edge-p))
          (fail build 'snowgrave:unclosed-class-operation :graph-state-container-closure
                "A native container can appear in an error payload; this state profile needs its captured closure to exclude private records."
                :reachability)))))
  (let ((writes nil) (unbinds nil))
    (labels ((invalidate (slot-form &optional unbindp)
               (multiple-value-bind (slot literalp) (quoted-value slot-form)
                 (when literalp
                   (pushnew slot writes)
                   (when unbindp (pushnew slot unbinds)))))
             (place (form)
               (when (and (consp form) (eq (car form) 'slot-value)) (invalidate (third form))))
             (walk (form)
               (when (and (consp form) (not (eq (car form) 'quote)))
                 (case (car form)
                   (setf (loop for tail on (cdr form) by #'cddr do (place (first tail))))
                   ((incf decf pop) (place (second form)))
                   ((push pushnew) (place (third form)))
                   (slot-makunbound (invalidate (third form) t))
                   ((snowgrave::%record-write snowgrave::%record-unbind)
                    (invalidate (third form) (eq (car form) 'snowgrave::%record-unbind))))
                 (mapc #'walk form))))
      (dolist (form (build-forms build))
        ;; A selected generated writer remains a root even without an early
        ;; caller. Its write cannot be omitted from the state obligation.
        (when (eq (defining-kind form) :class)
          (dolist (slot (fourth form))
            (when (consp slot)
              (loop for (option name) on (cdr slot) by #'cddr
                    when (and (member option '(:writer :accessor))
                              (member-name (if (eq option :accessor) (list 'setf name) name)
                                           (getf (build-declaration build) :closed-generics)))
                    do (pushnew (first slot) writes)))))
        (walk form)))
    (setf (build-graph-state-invalidations build) (list :writes writes :unbinds unbinds))))

(defun graph-record-slot-facts (build receiver slot)
  "Return captured boundness/value facts only for the exact private nodes."
  (let ((alternatives (domain-alternatives receiver)) (value :pending))
    (when (and alternatives (every #'graph-node-domain-p alternatives))
      (dolist (domain alternatives (values t value))
        (let* ((row (graph-node-row build domain))
               (field (assoc slot (getf row :slots))))
          (unless (and (getf row :class) field (second field)
                       (not (member slot (getf (build-graph-state-invalidations build) :unbinds))))
            (return (values nil :unknown)))
          (setf value (merge-value-domains
                       build value (if (member slot (getf (build-graph-state-invalidations build) :writes))
                                       :unknown (third field)))))))))

(defun record-slot-read-domain (build receiver-form slot-form)
  ;; Authored reads and MOP-generated readers use this one fact owner. A class
  ;; or declared slot type alone proves neither boundness nor restart result.
  (multiple-value-bind (slot literalp) (quoted-value slot-form)
    (if literalp
        (multiple-value-bind (boundp domain) (graph-record-slot-facts build (value-domain build receiver-form) slot)
          (values (if boundp domain :unknown) boundp))
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
          (cond ((member part '(:pending :unknown)) t)
                ((graph-node-domain-p part)
                 (let ((row (graph-node-row build part)))
                   (or (null row) (not (null (getf row :class))))))
                (t (some (lambda (row)
                           (let ((class (getf row :class)))
                             (and class (subtype-domain-p build class part))))
                         (build-graph-nodes build)))))
        (domain-alternatives domain)))

(defun audit-graph-record-slot (build receiver-form slot-form &key bound)
  (when (and (graph-state-profile-p build) (not *collect-function-flow*)
             (graph-private-record-domain-p build (value-domain build receiver-form)))
    (multiple-value-bind (slot literalp) (quoted-value slot-form)
      (let ((alternatives (domain-alternatives (value-domain build receiver-form))))
        (unless (and literalp alternatives
                     (every (lambda (domain)
                              (let* ((row (graph-node-row build domain)) (field (assoc slot (getf row :slots))))
                                (and (getf row :class) field
                                     (or (not bound)
                                         (and (second field)
                                              (not (member slot (getf (build-graph-state-invalidations build) :unbinds))))))))
                            alternatives))
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
       (audit-graph-native-inputs build (list (third arguments)) :graph-state-write))
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
                     (and (= count 2) (member name '(eq eql equal equalp))))
           (let ((receiver (native-sequence-argument-position name)))
             (loop for argument in arguments for position from 0
                   unless (and receiver (= position receiver) (native-sequence-form-p build argument))
                   do (audit-graph-native-inputs build (list argument) :graph-state-operation-input)))))))))

(defun audit-graph-entry-result (build name)
  (when (graph-state-profile-p build)
    (let ((summary (gethash name (build-function-returns build))))
      (unless (and (return-summary-p summary) (return-summary-completep summary)
                   (every (lambda (domain) (native-data-domain-p build domain)) (return-summary-domains summary)))
        (fail build 'snowgrave:unclosed-call :graph-state-result
              "Every public state entry must keep private records and dependent aggregates/callables behind its native result boundary."
              :reachability)))))

