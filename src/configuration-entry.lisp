(in-package #:snowgrave)

;;; A binding keeps its admitted facts; a generation owns only compiled code.
;;; Returned bridges never change identity when cold publication replaces code.
(defstruct configured-binding name entry arguments roles fields generation)
(defstruct configured-generation package function bridge mutations)

;; Keep post-commit housekeeping behind its own callable boundary.
(declaim (notinline discard-configuration-package))

(defun configuration-entry-name (unit entry)
  (let* ((metadata (find entry (getf (closed-unit-metadata unit) :entries)
                         :key (lambda (row) (getf row :name))))
         (key (getf metadata :code-key)))
    (find-symbol (second key) (first key))))

(defun index-configuration-functions (configuration)
  (dolist (form (closed-unit-source (configuration-unit configuration)))
    (when (eq (first form) 'defun)
      (setf (gethash (second form) (configuration-functions configuration))
            (list* 'defun (second form)
                   (rest (canonical-source (cons 'lambda (cddr form)))))))))

(defun compile-configured-entry (configuration entry arguments &optional bridge-name)
  (multiple-value-bind (body fact)
      (specialize-known-call configuration entry
                             (mapcar (lambda (value) (configured-value configuration value)) arguments)
                             (mapcar #'literal-fact arguments) nil)
    (when (or (fact-callable fact) (fact-owned-callable fact))
      (unsupported :configuration-indirect-call
                   "Configured entry returns an escaping callable value."))
    (let ((definitions (mapcar #'specialization-source
                               (nreverse (configuration-emitted configuration)))))
      ;; An ordinary entry specializes to one named root helper. Its argument
      ;; list is fixed by the binding recipe and remains stable across rebuilds.
      (unless (and (consp body) (find (first body) definitions :key #'second :test #'equal))
        (unsupported :configuration-source "Entry ~S did not produce a named root call." entry))
      ;; These are already direct specialized calls. Forcing every helper
      ;; INLINE duplicates shared call graphs (including escalation paths) and
      ;; can exhaust the host compiler before a bound entry is produced.
      (dolist (definition definitions) (compile-definition definition))
      (let ((function (fdefinition (first body))))
        (values function
                (when bridge-name
                  ;; The first target is private until publication. Compile
                  ;; captures in this generation's dynamic capture context.
                  (setf (fdefinition bridge-name) function)
                  (compile-function nil
                                    `(lambda () (declare (notinline ,bridge-name))
                                       (,bridge-name ,@(rest body)))
                                    :configuration-compilation)))))))

(defun discard-configuration-package (package)
  (do-symbols (symbol package)
    (when (and (eq (symbol-package symbol) package) (fboundp symbol))
      (fmakunbound symbol)))
  (delete-package package))

(defun compile-configuration-generation (unit binding write-fields)
  (let* ((package (make-package (format nil "SNOWGRAVE.GENERATION.~D"
                                       (incf *configuration-sequence*)) :use '("COMMON-LISP")))
         (configuration (make-configuration
                         :unit unit :roles (configured-binding-roles binding)
                         :fields (configured-binding-fields binding) :write-fields write-fields
                         :entry (intern "%IMPLEMENTATION" package)))
         (*configuration* configuration)
         (success nil))
    (unwind-protect
         (progn
           (index-configuration-functions configuration)
           (multiple-value-bind (function bridge)
               (compile-configured-entry
                configuration (configuration-entry-name unit (configured-binding-entry binding))
                (configured-binding-arguments binding)
                (unless (configured-binding-generation binding) (configured-binding-name binding)))
             (prog1 (make-configured-generation
                     :package package :function function :bridge bridge
                     :mutations (configuration-mutations configuration))
               (setf success t))))
      (unless success (discard-configuration-package package)))))

(defun configuration-generation-affected-p (binding changed)
  (loop for field being the hash-keys of
          (configured-generation-mutations (configured-binding-generation binding))
        thereis (gethash field changed)))

(defun publish-configured-bindings (unit binding registry generations wrappers)
  "Install only compiled definitions; restore all live state if commit fails."
  (let* ((old-seals (closed-unit-seals unit))
         (old-writers (closed-unit-sealed-writers unit))
         (old-bindings (closed-unit-configured-bindings unit))
         (new-bindings (cons binding old-bindings))
         (writers (make-hash-table :test #'equal))
         (definitions (append (loop for (recipe generation) in generations
                                    collect (list (configured-binding-name recipe)
                                                  (configured-generation-function generation)))
                              (loop for (name original function) in wrappers
                                    collect (list name function))))
         (old-definitions (loop for (name) in definitions
                                collect (list name (and (fboundp name) (fdefinition name)))))
         (old-generations (loop for (recipe) in generations
                                collect (list recipe (configured-binding-generation recipe))))
         (success nil))
    (maphash (lambda (name function) (setf (gethash name writers) function)) old-writers)
    (dolist (wrapper wrappers) (setf (gethash (first wrapper) writers) (second wrapper)))
    (unwind-protect
         (progn
           (dolist (definition definitions)
             (setf (fdefinition (first definition)) (second definition)))
           (dolist (row generations)
             (setf (configured-binding-generation (first row)) (second row)))
           (setf (closed-unit-seals unit) registry
                 (closed-unit-sealed-writers unit) writers
                 (closed-unit-configured-bindings unit) new-bindings
                 success t))
      (unless success
        (dolist (definition old-definitions)
          (if (second definition) (setf (fdefinition (first definition)) (second definition))
              (fmakunbound (first definition))))
        (dolist (row old-generations)
          (setf (configured-binding-generation (first row)) (second row)))
        (setf (closed-unit-seals unit) old-seals
              (closed-unit-sealed-writers unit) old-writers
              (closed-unit-configured-bindings unit) old-bindings)))
    old-generations))

(defun retire-configuration-generations (generations)
  ;; Code publication already succeeded. Housekeeping cannot revoke its result.
  (dolist (row generations)
    (when (second row)
      (handler-case
          (discard-configuration-package (configured-generation-package (second row)))
        (error (condition) (warn "Could not retire a replaced configuration package: ~A" condition))))))

(defun bind-entry (unit entry arguments &key roles)
  "Return a zero-argument function specialized for a fixed component graph.
ARGUMENTS are live closed values. ROLES contains (SOURCE-CLASS SLOT...)
declarations; a list in place of SLOT declares an exchange group of initially
validated component identities. Successful binding seals those roles through
the unit's writers and replaces affected configured implementations. Publication
must not race execution or another binding. Ordinary data remains mutable. The
function is host-local and has no independent configured-image export."
  (unit-function unit entry)
  (check-configuration-arguments unit entry arguments)
  (let* ((configuration (prepare-configuration unit arguments roles))
         (*configuration* configuration)
         (package (make-package (format nil "SNOWGRAVE.CONFIGURATION.~D"
                                        (incf *configuration-sequence*))
                                :use '("COMMON-LISP")))
         (binding (make-configured-binding
                   :name (intern "%BOUND-ENTRY" package) :entry entry :arguments (copy-list arguments)
                   :roles (configuration-roles configuration) :fields (configuration-fields configuration)))
         (generations nil) (success nil))
    (unwind-protect
         (progn
           (check-configuration-seals configuration)
           (multiple-value-bind (registry changed) (merged-configuration-seals configuration)
             (let ((write-fields (index-configuration-write-seals unit registry)))
               (dolist (recipe (if (zerop (hash-table-count changed)) (list binding)
                                  (cons binding (closed-unit-configured-bindings unit))))
                 (when (or (eq recipe binding) (configuration-generation-affected-p recipe changed))
                   (push (list recipe (compile-configuration-generation unit recipe write-fields)) generations))))
             (let* ((initial (second (assoc binding generations)))
                    (wrappers
                      (when (plusp (hash-table-count changed))
                        (loop for plan in (unit-plan-slots (closed-unit-plan unit))
                              when (member (slot-plan-operation plan) '(:write :unbind))
                                append (let ((wrapper (compile-sealed-writer configuration plan registry)))
                                         (when wrapper (list wrapper)))))))
               (let ((retired (publish-configured-bindings unit binding registry generations wrappers)))
                 ;; Retirement is post-commit housekeeping. Its failure must
                 ;; never trigger rollback cleanup of the published code.
                 (setf success t)
                 (retire-configuration-generations retired))
               (configured-generation-bridge initial))))
      (unless success
        (dolist (row generations)
          (discard-configuration-package (configured-generation-package (second row))))
        (discard-configuration-package package)))))
