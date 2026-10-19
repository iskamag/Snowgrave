(in-package #:snowgrave)

;; These are ordinary fixed records. No builder or MOP object belongs here.
;; Descriptor condition construction/FORMAT/interactive restarts are hosted
;; code. A supervisor adapter must admit or replace those complete paths.
(defstruct (record-layout (:constructor %make-layout))
  (identity nil :read-only t)
  (class-identity nil :type symbol :read-only t)
  (class nil :read-only t)
  (ancestors #() :read-only t)
  (slots #() :read-only t)
  (slot-types #() :read-only t)
  (row-token nil :read-only t)
  (reference-domain nil :read-only t)
  (reference-token nil :read-only t)
  (reference-class-index nil :read-only t)
  (reference-guards #() :read-only t)
  (error-mapping nil :read-only t))

(defun class-reference-slot-type-p (type classes)
  (labels ((walk (value seen)
             (or (and (symbolp value) (member value classes :test #'eq))
                 (and (consp value) (not (member value seen :test #'eq))
                      (eq (car value) 'and)
                      (handler-case (not (null (list-length value))) (type-error () nil))
                      (cdr value)
                      (every (lambda (part) (walk part (cons value seen))) (cdr value))))))
    (not (null (walk type nil)))))

(defun explicit-slot-type-p (type &optional classes)
  ;; Serializable declarations. Physical target layout is separately checked.
  (labels ((numeric (x)
             (or (member x '(t bit fixnum))
                 (and (consp x) (member (car x) '(unsigned-byte signed-byte))
                      (consp (cdr x)) (null (cddr x))
                      (typep (second x) '(integer 1 64)))))
           (array-type (x)
             (and (consp x) (eq (car x) 'simple-array)
                  (consp (cdr x)) (consp (cddr x)) (null (cdddr x))
                  (numeric (second x))
                  (or (eq (third x) '*)
                      (and (consp (third x)) (null (cdr (third x)))
                           (or (eq (car (third x)) '*)
                               (typep (car (third x)) '(integer 0))))))))
    (or (numeric type) (array-type type) (class-reference-slot-type-p type classes)
        (and (consp type) (eq (car type) 'or)
             ;; Finite proper unions; NULL is distinct from an array value.
             (handler-case (not (null (list-length type))) (type-error () nil))
             (eq (second type) 'null) (cddr type)
             (every #'array-type (cddr type))))))

(defun stable-identity-data-p (value &optional seen)
  (cond ((symbolp value) (not (null (symbol-package value))))
        ((or (stringp value) (numberp value) (characterp value)) t)
        ((consp value) (and (not (member value seen :test #'eq))
                           (stable-identity-data-p (car value) (cons value seen))
                           (stable-identity-data-p (cdr value) (cons value seen))))
        (t nil)))

(defun class-identity-token (identity class)
  ;; A readable interned token retains exact unit/version identity and EQ
  ;; across independent materializations of the same logical layout. Runtime
  ;; observation returns the token without copying or allocating.
  (unless (and (stable-identity-data-p identity) (symbolp class) (symbol-package class))
    (error "The class identity requires a stable readable unit key and interned class name."))
  (intern (with-standard-io-syntax (write-to-string (list identity class)))
          :snowgrave.class-identities))

(defun layout-row-token (identity class ancestors slots slot-types error-mapping)
  ;; Raw MAKE-LAYOUT historically accepted a wider logical subset (for example
  ;; uninterned slot names). Keep that behavior and detailed validation, but do
  ;; not grant such rows a canonical fast proof. Admitted source rows are stable.
  (let ((row (list :layout-row identity ancestors slots slot-types error-mapping)))
    (when (stable-identity-data-p row)
      (class-identity-token row class))))

(defstruct (reference-schema (:constructor %make-reference-schema))
  identity class ancestors slots slot-types error-mapping)

(defstruct (reference-domain (:constructor %make-reference-domain))
  (token nil :read-only t)
  (schemas #() :read-only t)
  (guards nil :read-only t))

(defun make-reference-domain (identity descriptions)
  "Build one shared, finite sealed class-reference domain for a unit.
DESCRIPTIONS use authored class/slot names and exact published logical layouts.
No MOP object or recursive expansion of reference types enters this table."
  (unless (and descriptions
               (handler-case (not (null (list-length descriptions))) (type-error () nil)))
    (error "Reference domains require finite nonempty logical layout rows."))
  (let* ((rows (sort (loop for description in descriptions
                          collect (list :identity (getf description :identity)
                                        :class (getf description :class)
                                        :ancestors (getf description :ancestors)
                                        :slots (getf description :slots)
                                        :slot-types (getf description :slot-types)
                                        :error-mapping (getf description :error-mapping)))
                     #'string< :key (lambda (row)
                                      (with-standard-io-syntax
                                        (write-to-string (source-name-key (getf row :class)))))))
         (classes (mapcar (lambda (row) (getf row :class)) rows)))
    (unless (= (length classes) (length (remove-duplicates classes :test #'eq)))
      (error "Duplicate class in sealed reference domain."))
    ;; The complete schema is part of the stable token. An equal unit name or
    ;; class spelling alone cannot bless an incompatible separately made layout.
    ;; Constructing/interning this readable identity is cold, never a hot write.
    (let ((token (class-identity-token (list :reference-domain identity rows) 'reference-domain)))
      (setf rows (immutable-copy rows))
      (dolist (row rows)
        (unless (and (equal identity (car (getf row :identity)))
                     (member (getf row :class) (getf row :ancestors) :test #'eq)
                     (every (lambda (ancestor) (member ancestor classes :test #'eq))
                            (getf row :ancestors))
                     (= (length (getf row :slots))
                        (length (remove-duplicates (getf row :slots) :test #'eq)))
                     (= (length (getf row :slots)) (length (getf row :slot-types)))
                     (every (lambda (type) (explicit-slot-type-p type classes)) (getf row :slot-types)))
          (error "Invalid sealed reference schema for ~S." (getf row :class))))
      (let* ((schemas (map 'vector
                           (lambda (row)
                             (%make-reference-schema
                              :identity (getf row :identity) :class (getf row :class)
                              :ancestors (coerce (getf row :ancestors) 'vector)
                              :slots (coerce (getf row :slots) 'vector)
                              :slot-types (coerce (getf row :slot-types) 'vector)
                              :error-mapping (getf row :error-mapping))) rows))
             (types (remove-duplicates
                     (loop for row in rows append
                           (remove-if-not (lambda (type) (class-reference-slot-type-p type classes))
                                          (getf row :slot-types))) :test #'equal)))
        (labels ((accepts-class-p (type schema)
                   (if (symbolp type)
                       (find type (reference-schema-ancestors schema) :test #'eq)
                       (every (lambda (part) (accepts-class-p part schema)) (cdr type)))))
          (%make-reference-domain
           :token token :schemas schemas
           :guards (loop for type in types
                         collect (cons type
                                       (map 'simple-bit-vector
                                            (lambda (schema) (if (accepts-class-p type schema) 1 0))
                                            schemas)))))))))

(defun sequence-list-equal-p (list vector &key (test #'eql))
  (and (= (length list) (length vector))
       (loop for expected in list for actual across vector always (funcall test expected actual))))

(defun make-layout (identity class ancestors slots &key error-mapping
                    (slot-types (make-list (length slots) :initial-element t)) reference-domain)
  "Construct the logical ABI layout from serializable class/slot identities."
  (when error-mapping
    (unless (and (equal (getf error-mapping :host-type) (lisp-implementation-type))
                 (equal (getf error-mapping :host-version) (lisp-implementation-version)))
      (error "The layout error mapping requires its recorded host implementation and version.")))
  (unless (and (member class ancestors :test #'equal)
               (= (length slots) (length (remove-duplicates slots :test #'eq)))
               (= (length slots) (length slot-types))
               (every (lambda (type)
                        (or (explicit-slot-type-p type)
                            (and reference-domain
                                 (assoc type (reference-domain-guards reference-domain) :test #'equal))))
                      slot-types))
    (error "Invalid Snowgrave logical layout for ~S." class))
  (if reference-domain
      (let* ((index (position class (reference-domain-schemas reference-domain)
                              :key #'reference-schema-class :test #'eq))
             (schema (and index (svref (reference-domain-schemas reference-domain) index))))
        (unless (and schema (equal identity (reference-schema-identity schema))
                     (sequence-list-equal-p ancestors (reference-schema-ancestors schema))
                     (sequence-list-equal-p slots (reference-schema-slots schema))
                     (sequence-list-equal-p slot-types (reference-schema-slot-types schema) :test #'equal)
                     (equal error-mapping (reference-schema-error-mapping schema)))
          (error "Layout does not match its sealed reference schema: ~S." class))
        (%make-layout :identity (reference-schema-identity schema)
                      :class-identity (class-identity-token identity class) :class class
                      :row-token (layout-row-token identity class ancestors slots slot-types error-mapping)
                      :ancestors (reference-schema-ancestors schema)
                      :slots (reference-schema-slots schema)
                      :slot-types (reference-schema-slot-types schema)
                      :error-mapping (reference-schema-error-mapping schema)
                      :reference-domain reference-domain
                      :reference-token (reference-domain-token reference-domain)
                      :reference-class-index index
                      :reference-guards
                      (map 'vector (lambda (type)
                                     (cdr (assoc type (reference-domain-guards reference-domain) :test #'equal)))
                           (reference-schema-slot-types schema))))
      (%make-layout :identity (immutable-copy identity)
                    :class-identity (class-identity-token identity class) :class class
                    :row-token (layout-row-token identity class ancestors slots slot-types error-mapping)
                    :ancestors (coerce ancestors 'vector)
                    :slots (map 'vector #'identity slots)
                    :slot-types (map 'vector #'immutable-copy slot-types)
                    :reference-guards (make-array (length slots) :initial-element nil)
                    :error-mapping (immutable-copy error-mapping))))

(defun layout-identity (layout)
  (immutable-copy (record-layout-identity layout)))

(defstruct (closed-record (:constructor %make-record (layout values bound)))
  (layout nil :type record-layout :read-only t)
  (values #() :type simple-vector :read-only t)
  (bound #* :type simple-bit-vector :read-only t))

(defun sg-make-record (layout)
  (let ((count (length (record-layout-slots layout))))
    (%make-record layout (make-array count :initial-element nil)
                  (make-array count :element-type 'bit :initial-element 0))))

(defun sg-record-p (value)
  (closed-record-p value))

(defun sg-record-class (record)
  (record-layout-class-identity (closed-record-layout record)))

(defun sg-record-unit-p (record identity)
  (and (closed-record-p record)
       (equal identity (car (record-layout-identity (closed-record-layout record))))))

(defun sg-record-layout-p (record identity class ancestors slots
                         &key (error-mapping nil error-mapping-p)
                           (slot-types nil slot-types-p)
                           (reference-domain nil reference-domain-p))
  "Validate the published logical layout, including version and CPL/slot shape."
  (and (closed-record-p record)
       (let ((layout (closed-record-layout record)))
         (and (equal identity (record-layout-identity layout))
              (eq class (record-layout-class layout))
              (or (not reference-domain-p)
                  (eq (and reference-domain (reference-domain-token reference-domain))
                      (record-layout-reference-token layout)))
              (or (not error-mapping-p)
                  (equal error-mapping (record-layout-error-mapping layout)))
              (= (length ancestors) (length (record-layout-ancestors layout)))
              (= (length slots) (length (record-layout-slots layout)))
              (loop for expected in ancestors for actual across (record-layout-ancestors layout)
                    always (eq expected actual))
              (loop for expected in slots for actual across (record-layout-slots layout)
                    always (eq expected actual))
              (if slot-types-p
                  (and (= (length slot-types) (length (record-layout-slot-types layout)))
                       (loop for expected in slot-types for actual across (record-layout-slot-types layout)
                             always (equal expected actual)))
                  (every (lambda (type) (eq type t)) (record-layout-slot-types layout)))))))

(defun sg-record-matches-layout-p (record admitted-layout)
  "Constant-cost exact admitted row test, with a separately required family.
An expected layout without a reference family imposes only its exact row. Raw
layouts outside the canonical serializable subset have no fast proof token."
  (and (closed-record-p record) (record-layout-p admitted-layout)
       (record-layout-row-token admitted-layout)
       (let ((actual (closed-record-layout record))
             (required-family (record-layout-reference-token admitted-layout)))
         (and (eq (record-layout-row-token admitted-layout) (record-layout-row-token actual))
              (or (null required-family)
                  (eq required-family (record-layout-reference-token actual)))))))

(defun sg-record-typep (record class)
  (and (closed-record-p record)
       (not (null (find class (record-layout-ancestors
                              (closed-record-layout record)) :test #'equal)))))

(defun native-slot-writer-value-p (value &optional seen)
  (or (symbolp value) (numberp value) (characterp value) (stringp value)
      (and (consp value) (not (member value seen :test #'eq))
           (let ((seen (cons value seen)))
             (and (native-slot-writer-value-p (car value) seen)
                  (native-slot-writer-value-p (cdr value) seen))))))

(defun record-slot-index (record slot operation &optional new-value)
  (or (position slot (record-layout-slots (closed-record-layout record))
                :test #'eq)
      (let* ((layout (closed-record-layout record))
             (mapping (record-layout-error-mapping layout)))
        (unless mapping
          (error "The slot ~S is missing from the Snowgrave record of class ~S."
                 slot (sg-record-class record)))
        (when (and (eq operation 'setf) (not (native-slot-writer-value-p new-value)))
          (sg-domain-violation (record-layout-identity layout) 'sg-record-write
                               (list record slot new-value)))
        (let ((hint (find slot (record-layout-slots layout) :test #'string-equal)))
          (error (getf mapping :missing-condition)
                 :name slot :format-control (getf mapping :missing-control)
                 :format-arguments
                 (list (if (eq operation 'setf)
                           (format nil (getf mapping :writer-control) new-value)
                           (cdr (assoc operation (getf mapping :operations))))
                       slot record
                       (when hint
                         (format nil (getf mapping :hint-control) hint slot))))))))

(defun sg-record-boundp (record slot)
  (= (sbit (closed-record-bound record) (record-slot-index record slot 'slot-boundp)) 1))

(defun read-slot-restart-value ()
  (format *query-io* "~&Enter a form to be evaluated: ")
  (finish-output *query-io*)
  (list (eval (read *query-io*))))

(defun sg-record-read (record slot)
  (let ((index (record-slot-index record slot 'slot-value)))
    (if (= (sbit (closed-record-bound record) index) 1)
        (svref (closed-record-values record) index)
        (let ((mapping (record-layout-error-mapping (closed-record-layout record))))
          (restart-case (error 'unbound-slot :instance record :name slot)
            (use-value (value)
              :report "Return a value as the slot-value."
              :interactive (lambda () (funcall (or (getf mapping :interactive)
                                                   #'read-slot-restart-value)))
              value)
            (store-value (value)
              :report "Store and return a value as the slot-value."
              :interactive (lambda () (funcall (or (getf mapping :interactive)
                                                   #'read-slot-restart-value)))
              (sg-record-write record slot value)))))))

(defun sg-record-write (record slot value)
  (let ((index (record-slot-index record slot 'setf value)))
    (let* ((layout (closed-record-layout record))
           (type (svref (record-layout-slot-types layout) index))
           (guard (svref (record-layout-reference-guards layout) index)))
      (unless (if guard
                  (and (closed-record-p value)
                       (let* ((actual (closed-record-layout value))
                              (class-index (record-layout-reference-class-index actual)))
                         (and (eq (record-layout-reference-token layout)
                                  (record-layout-reference-token actual))
                              (typep class-index 'fixnum) (<= 0 class-index) (< class-index (length guard))
                              (= 1 (sbit guard class-index)))))
                  (or (eq type t) (typep value type)))
        (error 'type-error :datum value :expected-type type)))
    (setf (svref (closed-record-values record) index) value
          (sbit (closed-record-bound record) index) 1)
    value))

(defun (setf sg-record-read) (value record slot)
  (sg-record-write record slot value))

(defun sg-record-unbind (record slot)
  (let ((index (record-slot-index record slot 'slot-makunbound)))
    ;; Release an unbound reference rather than keeping it as a hidden root.
    (setf (svref (closed-record-values record) index) nil
          (sbit (closed-record-bound record) index) 0)
    nil))

;; Compiler-owned annotations retain the proven receiver layouts. They do not
;; change the public record ABI, and the portable implementation keeps its
;; ordinary errors/restarts. Target preparation may consume these literals.
(defun %record-read (record slot classes)
  (declare (ignore classes)) (sg-record-read record slot))
(defun %record-write (record slot value classes)
  (declare (ignore classes)) (sg-record-write record slot value))
(defun (setf %record-read) (value record slot classes)
  (%record-write record slot value classes))
(defun %record-boundp (record slot classes)
  (declare (ignore classes)) (sg-record-boundp record slot))
(defun %record-unbind (record slot classes)
  (declare (ignore classes)) (sg-record-unbind record slot))
