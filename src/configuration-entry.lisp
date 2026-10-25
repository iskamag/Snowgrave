(in-package #:snowgrave)

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

(defun compile-configured-entry (configuration entry arguments)
  (multiple-value-bind (body fact)
      (specialize-known-call configuration entry
                             (mapcar (lambda (value) (configured-value configuration value)) arguments)
                             (mapcar #'literal-fact arguments) nil)
    (when (or (fact-callable fact) (fact-owned-callable fact))
      (unsupported :configuration-indirect-call
                   "Configured entry returns an escaping callable value."))
    (let ((definitions (mapcar #'specialization-source
                               (nreverse (configuration-emitted configuration)))))
      ;; These are already direct specialized calls. Forcing every helper
      ;; INLINE duplicates shared call graphs (including escalation paths) and
      ;; can exhaust the host compiler before a bound entry is produced.
      (dolist (definition definitions) (compile-definition definition))
      (compile-function (configuration-entry configuration) `(lambda () ,body)
                        :configuration-compilation))))

(defun discard-configuration-package (package)
  (do-symbols (symbol package)
    (when (and (eq (symbol-package symbol) package) (fboundp symbol))
      (fmakunbound symbol)))
  (delete-package package))

(defun bind-entry (unit entry arguments &key roles)
  "Return a zero-argument function specialized for a fixed component graph.
ARGUMENTS are live closed values. ROLES contains (SOURCE-CLASS SLOT...)
declarations; a list in place of SLOT declares an exchange group of initially
validated component identities. Successful binding seals those roles through
the unit's writers. Ordinary data remains mutable. The function is host-local
and has no independent configured-image export."
  (unit-function unit entry)
  (check-configuration-arguments unit entry arguments)
  (let* ((configuration (prepare-configuration unit arguments roles))
         (*configuration* configuration)
         (package (make-package (format nil "SNOWGRAVE.CONFIGURATION.~D"
                                        (incf *configuration-sequence*))
                                :use '("COMMON-LISP")))
         (success nil))
    (unwind-protect
         (progn
           (check-configuration-seals configuration)
           (setf (configuration-entry configuration) (intern "%BOUND-ENTRY" package))
           (index-configuration-functions configuration)
           (let ((function (compile-configured-entry
                            configuration (configuration-entry-name unit entry) arguments)))
             ;; Only publish seals after every specialization has compiled.
             (publish-configuration-seals configuration)
             (setf success t)
             function))
      (unless success (discard-configuration-package package)))))
