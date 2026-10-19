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
  (configuration-bindings nil :read-only t)
  (report nil :read-only t))

(defun unit-metadata (unit)
  (immutable-copy (closed-unit-metadata unit)))

(defun unit-source (unit)
  (immutable-copy (closed-unit-source unit)))

(defun unit-report (unit)
  (immutable-copy (closed-unit-report unit)))

(defun function-name-key (name) (source-name-key name))

(defun unit-binding-key (unit name)
  (let ((bindings (remove-duplicates
                   (append (closed-unit-bindings unit) (closed-unit-configuration-bindings unit))
                   :key #'car :test #'equal)))
    (if (stringp name)
        (let ((matches (remove-if-not
                        (lambda (binding)
                          (let ((key (car binding)))
                            (and (stringp (car key)) (string= name (second key)))))
                        bindings)))
          (when (= (length matches) 1) (caar matches)))
        (function-name-key name))))

(defun unit-function (unit name &key bind-configuration)
  "Resolve an installed entry. BIND-CONFIGURATION explicitly selects its
zero-argument fixed-root binding; the artifact retains its original arity."
  (let* ((key (unit-binding-key unit name))
         (configured (cdr (assoc key (closed-unit-configuration-bindings unit) :test #'equal))))
    (when configured
      (unless bind-configuration
        (error "Entry ~S requires :BIND-CONFIGURATION T for its fixed-root binding." name))
      (return-from unit-function configured))
    (when bind-configuration (error "Entry ~S has no fixed configuration binding." name))
    (or (cdr (assoc key (closed-unit-bindings unit) :test #'equal))
        (error "~S is not an entry of Snowgrave unit ~S."
               name (getf (closed-unit-metadata unit) :identity)))))

(defstruct (identity-operand (:constructor make-identity-operand (value))) value)

(defun own-closing-declaration (declaration)
  "Own structural data without copying identity operands before joint capture.
An object used both as an identity operand and as metadata still has an owned
metadata copy. Temporary handles occur only at explicit operand positions."
  (labels ((entry-map (entries function)
             (if (source-finite-list-p entries)
                 (mapcar (lambda (entry)
                           (if (and (source-finite-list-p entry) (= (length entry) 2)
                                    (source-finite-list-p (second entry)))
                               (list (first entry)
                                     (mapcar (lambda (domain)
                                               (if (and (consp domain) (source-finite-list-p domain)
                                                        (= (length domain) 2) (eq (first domain) 'eql))
                                                   (list 'eql (funcall function (second domain))) domain))
                                             (second entry))) entry)) entries) entries))
           (binding-map (bindings function)
             (if (source-finite-list-p bindings)
                 (mapcar (lambda (binding)
                           (if (and (source-finite-list-p binding) (= (length binding) 2))
                               (list (first binding) (funcall function (second binding))) binding)) bindings)
                 bindings)))
    (let ((skeleton (copy-list declaration)))
      (setf (getf skeleton :external-domains)
            (entry-map (getf skeleton :external-domains) #'make-identity-operand)
            (getf skeleton :native-bindings)
            (binding-map (getf skeleton :native-bindings) #'make-identity-operand))
      (let ((owned (immutable-copy skeleton)))
        (setf (getf owned :external-domains)
              (entry-map (getf owned :external-domains) #'identity-operand-value)
              (getf owned :native-bindings)
              (binding-map (getf owned :native-bindings) #'identity-operand-value))
        owned))))

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
                       ((or (consp x) (arrayp x))
                        (unless (gethash x seen)
                          (setf (gethash x seen) t)
                          (if (consp x) (progn (collect (car x)) (collect (cdr x)))
                              (multiple-value-bind (parent offset) (array-displacement x)
                                (declare (ignore offset))
                                (if parent (collect parent)
                                    (unless (null (array-element-type x))
                                      (dotimes (index (array-total-size x))
                                        (collect (row-major-aref x index))))))))))))
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
                           external-value-guards external-argument-domains native-bindings
                           (domain-violation :signal) (adapter :sbcl)
                         &allow-other-keys)
  "Close an ordered source unit through a registered compiler adapter.
No unit is returned until the adapter's semantic and residual audits pass.
Identity-bearing EQL entry operands request joint cold graph capture. Native
array bindings are (stable-key array) pairs whose identities are preserved;
other captured storage becomes a private installed copy without initialization.
Successful closing adopts this source configuration exclusively: the caller
must stop using its original mutation and cleanup routes. Failure retains the
original configuration's custody. Native installation owners maintain admitted
geometry, alias relations and external resource lifetime. Resolve such entries
with UNIT-FUNCTION :BIND-CONFIGURATION T; their bindings take no arguments.
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
    (flet ((close-it () (funcall closer source-unit (own-closing-declaration declaration))))
      (if native-bindings
          (call-with-native-bindings unit-name native-bindings #'close-it)
          (close-it)))))
