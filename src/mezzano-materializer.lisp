(in-package #:snowgrave)

(defun audit-mezzano-reader-data (data)
  ;; Target reading precedes macroexpansion. Even a quoted diagnostic or
  ;; descriptor needs its symbol's package before a native mapper can run.
  (let ((seen (make-hash-table :test #'eq)))
    (labels ((walk (value)
               (cond ((symbolp value)
                      (let ((package (symbol-package value)))
                        (when (and package (eql 0 (search "SB-" (package-name package))))
                          (reject 'unsupported-definition :native-materialization :native-host-package
                                  (format nil "Host symbol ~S has no target reader/package mapping." value)))))
                     ((or (consp value) (simple-vector-p value))
                      (unless (gethash value seen)
                        (setf (gethash value seen) t)
                        (if (consp value) (progn (walk (car value)) (walk (cdr value)))
                            (map nil #'walk value)))))))
      (walk data))))

(defun write-mezzano-unit-source (unit stream &key (area :wired))
  "Prepare native record source from an audited portable unit.
This is cold source preparation, NOT supervisor code/data/error admission.
The target compiler finalizes the generated structures and validates every
field against its actual native layout before compiling the original CEM.
Unmapped implementation-specific conditions and reader packages refuse
preparation, including symbols carried in quoted forms and metadata."
  (unless (member area '(:wired :dynamic))
    (reject 'unsupported-definition :native-materialization :record-area
            "Only the target's ordinary :WIRED and :DYNAMIC areas are supported."))
  (let ((forms (unit-source unit)) (metadata (unit-metadata unit)) (type-obligations nil))
    (when (getf metadata :configuration)
      (reject 'unsupported-definition :native-materialization :configuration-installation-abi
              "Fixed configuration capture needs a target installation and custody mapping before native preparation."))
    (labels ((audit (form)
               (cond ((symbolp form)
                      (when (and (symbol-package form)
                                 (string= (package-name (symbol-package form)) "SB-PCL"))
                        (reject 'unsupported-definition :native-materialization :native-condition-abi
                                (format nil "Executable host condition/operation ~S has no native mapping." form))))
                     ((consp form)
                      (when (and (eq (car form) 'typep) (consp (third form))
                                 (eq (car (third form)) 'quote))
                        ;; Source partitions can contain host builtin types
                        ;; absent on the target. Keep every actual type as an
                        ;; explicit target ABI obligation; a spelling is not
                        ;; evidence of equivalent target semantics.
                        (pushnew (second (third form)) type-obligations :test #'equal))
                      (when (and (member (car form) '(error signal make-condition))
                                 (consp (second form)) (eq (car (second form)) 'quote))
                        ;; A literal condition argument is executable even
                        ;; though its name is syntactically quoted.
                        (let ((name (second (second form))))
                          (unless (and (symbolp name) (symbol-package name)
                                       (string= (package-name (symbol-package name)) "SB-PCL")
                                       (string= (symbol-name name) "NO-APPLICABLE-METHOD-ERROR"))
                            (audit name))))
                      ;; Quoted descriptor data is not an executable error ABI.
                      (unless (eq (car form) 'quote)
                        (audit (car form)) (audit (cdr form)))))))
      (dolist (form forms) (audit form)))
    (setf (getf metadata :native-type-obligations) (nreverse type-obligations))
    (setf (getf metadata :native-generic-bindings)
          (loop for dispatch in (getf metadata :dispatch)
                for generic = (getf dispatch :generic)
                for definition = (find (function-name-key generic) (getf metadata :definitions)
                                       :key (lambda (x) (third (getf x :definition-key))) :test #'equal)
                for code = (getf definition :code-key)
                do (unless code
                     (reject 'unsupported-definition :native-materialization :generic-code-binding
                             "The frozen generic lacks its emitted code identity."))
                collect (list :generic generic :lambda-list (getf dispatch :lambda-list)
                              :code-name (if (eq (car code) 'setf)
                                             (list 'setf (intern (second (second code)) (first (second code))))
                                             (intern (second code) (first code))))))
    ;; Audit the complete target payload before writing anything. Quoting data
    ;; cannot exempt it from the target reader's package requirements.
    (audit-mezzano-reader-data (list forms metadata))
    ;; Reuse the portable serializer's package/reader-sharing rules. Its final
    ;; PROGN is replaced with one target macro; no builder survives in output.
    (let* ((text (with-output-to-string (out) (write-unit-source unit out)))
           (*package* (find-package :cl))
           (read-forms (with-input-from-string (in text)
                         (loop for form = (read in nil in) until (eq form in) collect form))))
      (let ((*print-readably* nil) (*print-escape* t) (*print-pretty* t) (*print-circle* t))
        (dolist (form (butlast read-forms)) (write form :stream stream) (terpri stream))
        (write `(snowgrave.mezzano-materializer:define-materialized-unit
                    ,metadata ,forms ,area) :stream stream)
        (terpri stream)))
    metadata))
