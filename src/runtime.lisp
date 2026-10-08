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
  (error-mapping nil :read-only t))

(defun explicit-slot-type-p (type)
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
    (or (numeric type) (array-type type)
        (and (consp type) (eq (car type) 'or)
             ;; Finite proper unions; NULL is distinct from an array value.
             (handler-case (not (null (list-length type))) (type-error () nil))
             (eq (second type) 'null) (cddr type)
             (every #'array-type (cddr type))))))

(defun class-identity-token (identity class)
  ;; A readable interned token retains exact unit/version identity and EQ
  ;; across independent materializations of the same logical layout. Runtime
  ;; observation returns the token without copying or allocating.
  (labels ((stable (value seen)
             (cond ((symbolp value) (not (null (symbol-package value))))
                   ((or (stringp value) (numberp value) (characterp value)) t)
                   ((consp value) (and (not (member value seen :test #'eq))
                                      (stable (car value) (cons value seen))
                                      (stable (cdr value) (cons value seen))))
                   (t nil))))
    (unless (and (stable identity nil) (symbolp class) (symbol-package class))
      (error "The class identity requires a stable readable unit key and interned class name.")))
  (intern (with-standard-io-syntax (write-to-string (list identity class)))
          :snowgrave.class-identities))

(defun make-layout (identity class ancestors slots &key error-mapping (slot-types (make-list (length slots) :initial-element t)))
  "Construct the logical ABI layout from serializable class/slot identities."
  (when error-mapping
    (unless (and (equal (getf error-mapping :host-type) (lisp-implementation-type))
                 (equal (getf error-mapping :host-version) (lisp-implementation-version)))
      (error "The layout error mapping requires its recorded host implementation and version.")))
  (unless (and (member class ancestors :test #'equal)
               (= (length slots) (length (remove-duplicates slots :test #'eq)))
               (= (length slots) (length slot-types))
               (every #'explicit-slot-type-p slot-types))
    (error "Invalid Snowgrave logical layout for ~S." class))
  (%make-layout :identity (immutable-copy identity)
                :class-identity (class-identity-token identity class) :class class
                :ancestors (coerce ancestors 'vector)
                :slots (map 'vector #'identity slots)
                :slot-types (map 'vector #'immutable-copy slot-types)
                :error-mapping (immutable-copy error-mapping)))

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
                           (slot-types nil slot-types-p))
  "Validate the published logical layout, including version and CPL/slot shape."
  (and (closed-record-p record)
       (let ((layout (closed-record-layout record)))
         (and (equal identity (record-layout-identity layout))
              (eq class (record-layout-class layout))
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
    (let ((type (svref (record-layout-slot-types (closed-record-layout record)) index)))
      (unless (or (eq type t) (typep value type))
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
