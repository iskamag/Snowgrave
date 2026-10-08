(in-package #:snowgrave)

(defvar *source-adapters* (make-hash-table :test #'eq))

(defun register-source-adapter (name function)
  (check-type function function)
  (setf (gethash name *source-adapters*) function)
  name)

(defstruct (closed-unit (:constructor %make-unit))
  (metadata nil :read-only t)
  (source nil :read-only t)
  (bindings nil :read-only t)
  (report nil :read-only t))

(defun unit-metadata (unit)
  (immutable-copy (closed-unit-metadata unit)))

(defun unit-source (unit)
  (immutable-copy (closed-unit-source unit)))

(defun unit-report (unit)
  (immutable-copy (closed-unit-report unit)))

(defun function-name-key (name) (source-name-key name))

(defun unit-function (unit name)
  "Resolve an externally callable entry in this installed portable binding."
  (or (if (stringp name)
          (let ((matches (remove-if-not (lambda (binding)
                                         (let ((key (car binding)))
                                           (and (stringp (car key)) (string= name (second key)))))
                                       (closed-unit-bindings unit))))
            (when (= (length matches) 1) (cdar matches)))
          (cdr (assoc (function-name-key name) (closed-unit-bindings unit) :test #'equal)))
      (error "~S is not an entry of Snowgrave unit ~S."
             name (getf (closed-unit-metadata unit) :identity))))

(defun write-unit-source (unit stream)
  (let ((*print-readably* t) (*print-pretty* t) (*print-circle* t) (*package* (find-package :cl)))
    (write '(in-package #:common-lisp) :stream stream)
    (terpri stream)
    (let ((packages nil) (shadows nil) (exports nil) (seen (make-hash-table :test #'eq)))
      (labels ((collect (x)
                 (cond ((symbolp x)
                        (let ((package (symbol-package x)))
                          (when (and package
                                     (not (member (package-name package)
                                                  '("COMMON-LISP" "KEYWORD" "SNOWGRAVE") :test #'string=)))
                            (pushnew (package-name package) packages :test #'string=)
                            (when (eq (nth-value 1 (find-symbol (symbol-name x) package)) :external)
                              (pushnew (cons (package-name package) (symbol-name x)) exports :test #'equal))
                            (let ((common (find-symbol (symbol-name x) :cl)))
                              (when (and common (not (eq common x)))
                                (pushnew (cons (package-name package) (symbol-name x)) shadows
                                         :test #'equal))))))
                       ((or (consp x) (simple-vector-p x))
                        (unless (gethash x seen)
                          (setf (gethash x seen) t)
                          (if (consp x) (progn (collect (car x)) (collect (cdr x)))
                              (loop for part across x do (collect part))))))))
        (collect (closed-unit-source unit))
        ;; Metadata can mention exported source names absent from emitted code,
        ;; such as an entry whose zero-argument body is a scalar constant.
        (collect (closed-unit-metadata unit)))
      (dolist (name (sort packages #'string<))
        (write `(eval-when (:compile-toplevel :load-toplevel :execute)
                  (unless (find-package ,name) (make-package ,name :use '("COMMON-LISP")))
                  ,@(when (assoc name shadows :test #'string=)
                      `((shadow ',(sort (loop for (package . symbol) in shadows
                                             when (string= package name) collect symbol)
                                       #'string<)
                                ,name)))
                  ,@(when (assoc name exports :test #'string=)
                      `((export (mapcar (lambda (symbol-name) (intern symbol-name ,name))
                                       ',(sort (loop for (package . symbol) in exports
                                                     when (string= package name) collect symbol)
                                               #'string<))
                                ,name)))) :stream stream)
        (terpri stream)))
    ;; Reader labels have one whole-form scope. Preserve sharing between
    ;; constructor initforms and ordinary definitions as well as inside each.
    (write `(progn ,@(closed-unit-source unit)) :stream stream)
    (terpri stream)))

(defun write-unit-metadata (unit stream)
  (let ((*print-readably* t) (*print-pretty* nil) (*print-circle* t) (*package* (find-package :cl)))
    (write (closed-unit-metadata unit) :stream stream)
    (terpri stream)))

(defun close-source-unit (source-unit &rest declaration
                         &key unit-name closed-classes universe closed-generics
                           entries external-domains external-operations external-return-domains
                           external-value-guards external-argument-domains
                           (domain-violation :signal) (adapter :sbcl)
                         &allow-other-keys)
  "Close an ordered source unit through a registered compiler adapter.
No unit is returned until the adapter's semantic and residual audits pass.
EXTERNAL-RETURN-DOMAINS optionally records (operation exact-native-value-tuple)
owner ABI guarantees. It grants no purity, placement, or opaque-object proof;
an installed external binding must satisfy its published result contract.
EXTERNAL-VALUE-GUARDS records (owner-key predicate native-structure-type): an
ordinary one-argument BOOLEAN predicate must reject foreign logical values by
identity before interpretation, and establish a live unchanged native authority.
Positive lexical checks establish (:EXTERNAL-VALUE owner-key). They grant no
nominal cohort interpretation or target admission. EXTERNAL-ARGUMENT-DOMAINS
requires each external call's exact value tuple; corresponding result promises
apply only on that tuple. Opaque returned keys must forward an already guarded
argument authority. Definition/resource/alias lifetime remains installation-owned."
  (declare (ignore closed-classes universe closed-generics external-domains
                   external-operations external-return-domains external-value-guards external-argument-domains))
  (unless (and unit-name entries)
    (reject 'unsupported-definition :declaration :unit-identity-and-entries
            "Both an immutable unit identity and ordinary-function entries are required."))
  (unless (eq domain-violation :signal)
    (reject 'unsupported-definition :declaration :violation-action
            "This portable binding supplies only the non-returning :SIGNAL action."))
  (let ((closer (gethash adapter *source-adapters*)))
    (unless closer
      (reject 'unsupported-definition :declaration :adapter
              (format nil "Load the compiler adapter for ~S before closing." adapter)))
    (funcall closer source-unit (immutable-copy declaration))))
