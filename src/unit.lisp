(in-package #:snowgrave)

(defstruct (closed-unit (:constructor %make-unit (metadata source bindings plan)))
  metadata source bindings plan
  (seals (make-hash-table :test #'eq))
  (sealed-writers (make-hash-table :test #'equal))
  (configured-bindings nil))

(defvar *unit-sequence* 0)

(defun unit-metadata (unit) (copy-source-graph (closed-unit-metadata unit)))

(defun unit-source (unit) (copy-source-graph (closed-unit-source unit)))

(defun unit-report (unit)
  (list :mechanism :mop-two-pass :profile :source-core
        :target-accepted nil :configuration-capture nil
        :classes (length (getf (closed-unit-metadata unit) :classes))))

(defun unit-function (unit name)
  (or (cdr (assoc name (closed-unit-bindings unit) :test #'equal))
      (error "Not a public entry: ~S." name)))

(defun compile-function (name source &optional (feature :compilation))
  (multiple-value-bind (function warnings failure) (compile name source)
    (declare (ignore warnings))
    (when failure (unsupported feature "The host could not compile ~S." (or name feature)))
    function))

(defun compile-definition (form)
  (funcall (compile-function nil (list 'lambda nil form))))

(defun make-unit-plan-from-build (build)
  ;; These are plain source descriptions, never open MOP objects. Keep enough
  ;; information for a configured entry without reopening the class world.
  (make-unit-plan
   :package (package-name (build-output-package build))
   :generics (build-generic-plans build)
   :special-variables (loop for form in (build-forms build)
                           when (member (first form) '(defvar defparameter))
                             collect (closed-name build (second form)))
   :entries (loop for (name domains) in (getf (build-declaration build) :external-domains)
                  collect (list name (mapcar (lambda (type) (rewrite-type build type :closed)) domains)))
   :slots (build-slot-plans build)
   :accessor-functions (build-accessor-functions build)
   :slow-paths (mapcar (lambda (name) (closed-name build name))
                       '(%record-invalid-slot %record-unbound))
   :construction-functions (when (build-layouts build)
                             (cons (record-make-instance-name build :closed)
                                   (loop for layout in (build-layouts build)
                                         append (list (class-description-constructor layout)
                                                      (class-description-allocator layout)))))
   :layouts (build-layouts build)))

(defun discard-builder (build)
  (let ((package (build-open-package build)))
    (do-symbols (symbol package)
      (when (eq (symbol-package symbol) package)
        (when (fboundp symbol) (fmakunbound symbol))
        (when (fboundp (list 'setf symbol)) (fmakunbound (list 'setf symbol)))
        (when (and (boundp symbol) (not (constantp symbol))) (makunbound symbol))
        (when (find-class symbol nil) (setf (find-class symbol) nil))))
    (delete-package package)))

(defun validate-close-declaration (declaration unit-name entries adapter domain-violation)
  (loop for (key value) on declaration by #'cddr
        unless (member key '(:unit-name :entries :closed-classes :closed-generics :universe
                             :external-domains :external-operations :domain-violation :adapter))
        do (unsupported :declaration "Unsupported source-core option ~S = ~S." key value))
  (unless (and unit-name entries (member adapter '(:portable :sbcl))
               (eq domain-violation :signal))
    (unsupported :declaration "A named unit, public entries and :SIGNAL policy are required.")))

(defun validate-owned-cohort (build)
  (let ((declaration (build-declaration build)))
    (loop for (key actual) in (list (list :closed-classes (build-classes build))
                                    (list :closed-generics (build-generics build)))
          when (loop for tail on declaration by #'cddr thereis (eq (first tail) key))
          do (let ((selected (getf declaration key)))
               (unless (and (null (set-difference actual selected :test #'equal))
                            (null (set-difference selected actual :test #'equal)))
                 (unsupported :partial-cohort
                              "~S must name the complete owned set ~S." key actual))))
    (dolist (entry (getf declaration :entries))
      (unless (member entry (build-functions build) :test #'equal)
        (unsupported :entry "Entry ~S needs an owned ordinary definition." entry)))))

(defun compile-open-cohort (build)
  (prepare-open-generics build)
  (let* ((forms (mapcar (lambda (form) (open-definition build form)) (build-forms build)))
         (literals (literal-definition build :open)))
    (emit-open-record-helpers build)
    (when literals (compile-definition literals))
    (dolist (form forms) (compile-definition form))))

(defun generate-closed-source (build)
  (prepare-records build)
  (scan-usage build)
  (emit-form build
             `(define-condition ,(closed-name build '%program-error)
                  (simple-condition program-error) ()))
  (emit-records build)
  (when (usage-needs-metadata-p (build-usage build)) (emit-metadata build))
  (when (usage-flag-p (build-usage build) 'equalp) (emit-observations build))
  (emit-generics build)
  (emit-functions build)
  (let ((literals (literal-definition build :closed))
        (specials (loop for form in (build-forms build)
                        when (member (first form) '(defvar defparameter))
                        collect (closed-name build (second form)))))
    (append (when specials (list (list 'declaim (cons 'special specials))))
            (when literals (list literals))
            (nreverse (build-generated build)))))

(defun make-unit-metadata (build)
  (list :identity (build-identity build)
        :mechanism :mop-two-pass
        :profile :source-core
        :classes (copy-list (build-classes build))
        :entries (loop for name in (getf (build-declaration build) :entries)
                       for symbol = (closed-name build name)
                       collect (list :name name
                                     :code-key (list (package-name (symbol-package symbol))
                                                     (symbol-name symbol))))))

(defun compile-closed-unit (build)
  (let ((forms (generate-closed-source build)))
    (check-residual-source build forms)
    (dolist (form forms) (compile-definition form))
    (%make-unit (make-unit-metadata build) forms
                (loop for name in (getf (build-declaration build) :entries)
                      collect (cons name (fdefinition (closed-name build name))))
                (make-unit-plan-from-build build))))

(defun close-source-unit (source &rest declaration
                          &key unit-name entries closed-classes closed-generics universe
                            external-domains external-operations (domain-violation :signal)
                            (adapter :portable)
                            &allow-other-keys)
  "Close an ordered (:FORMS forms) or (:FILES pathname...) source cohort.
ENTRIES names owned ordinary functions. EXTERNAL-DOMAINS supplies one declared
domain per required entry parameter. Unsupported source signals SNOWGRAVE-ERROR.
Source initialization runs once in each compilation namespace."
  (declare (ignore closed-classes closed-generics universe external-domains external-operations))
  (validate-close-declaration declaration unit-name entries adapter domain-violation)
  ;; Read before allocating namespaces: reader/package errors must not leak them.
  (let* ((forms (read-source source))
         (number (incf *unit-sequence*))
         (open (make-package (format nil "SNOWGRAVE.BUILD.~D" number) :use '(:cl)))
         (output (make-package (format nil "SNOWGRAVE.CLOSED.~D" number) :use '(:cl)))
         (build (make-build :identity (copy-source-graph unit-name)
                            :declaration (copy-source-graph declaration)
                            :forms forms :open-package open :output-package output))
         (success nil))
    (setf (build-open-literal-name build) (intern "%LITERALS" open)
          (build-closed-literal-name build) (intern "%LITERALS" output))
    (unwind-protect
         (progn
           (index-source build)
           (normalize-owned-source build)
           (validate-owned-cohort build)
           ;; Refuse custom initialization before installing any host methods.
           (validate-record-protocol build)
           (compile-open-cohort build)
           (prog1 (compile-closed-unit build)
             (setf success t)))
      (discard-builder build)
      (unless success (delete-package output)))))
