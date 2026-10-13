(in-package #:snowgrave.tests)

(defun native-materialization-tests ()
  (let* ((type '(or null (simple-array (unsigned-byte 8) (*))
                        (simple-array (unsigned-byte 16) (*))
                        (simple-array (unsigned-byte 32) (*))))
         (layout (snowgrave:make-layout '(:array-union) 'array-owner '(array-owner) '(data)
                                      :slot-types (list type)))
         (record (snowgrave:sg-make-record layout)))
    (check (not (snowgrave:sg-record-boundp record 'data)))
    (dolist (element-type '((unsigned-byte 8) (unsigned-byte 16) (unsigned-byte 32)))
      (let ((data (make-array 3 :element-type element-type)))
        (check (eq data (snowgrave:sg-record-write record 'data data)))
        (check (eq data (snowgrave:sg-record-read record 'data)))))
    (let ((held (snowgrave:sg-record-read record 'data)))
      (dolist (invalid (list :invalid (make-array 3) (make-array 3 :element-type '(unsigned-byte 64))
                            (make-array '(2 2) :element-type '(unsigned-byte 8))))
        (signals type-error (snowgrave:sg-record-write record 'data invalid))
        (check (eq held (snowgrave:sg-record-read record 'data)))))
    (check (null (snowgrave:sg-record-write record 'data nil)))
    (check (snowgrave:sg-record-boundp record 'data))
    (snowgrave:sg-record-unbind record 'data)
    (check (not (snowgrave:sg-record-boundp record 'data)))
    (signals unbound-slot (snowgrave:sg-record-read record 'data))
    (check (not (snowgrave::explicit-slot-type-p '(or null fixnum))))
    (check (not (snowgrave::explicit-slot-type-p '(or null (simple-array (unsigned-byte 8) (*)) . invalid))))
    (let ((cycle (list 'or 'null '(simple-array (unsigned-byte 8) (*)))))
      (setf (cdr (last cycle)) cycle)
      (check (not (snowgrave::explicit-slot-type-p cycle)))))
  ;; Executable implementation-specific conditions are never treated as
  ;; harmless quoted layout metadata by the target writer.
  (let ((unit (snowgrave::%make-unit
               :metadata '(:identity (:unmapped-native))
               :source '((defun native-missing () (error 'sb-pcl::no-next-method-error))))))
    (signals snowgrave:unsupported-definition
      (with-output-to-string (out) (snowgrave:write-mezzano-unit-source unit out))))
  (let* ((type '(complex double-float))
         (unit (snowgrave::%make-unit
                :metadata '(:identity (:native-type-obligation))
                :source `((defun native-partition (value) (typep value ',type)))))
         (metadata (with-open-stream (out (make-string-output-stream))
                     (snowgrave:write-mezzano-unit-source unit out))))
    (check (equal (getf metadata :native-type-obligations) (list type))))
  ;; These symbols used to escape through quoted layout/error descriptors.
  ;; Preparation must refuse before the first byte reaches the target stream.
  (dolist (host '(sb-pcl::missing-slot sb-int:read-evaluated-form
                  sb-ext:print-symbol-with-prefix sb-kernel:complex-double-float))
    (dolist (unit (list (snowgrave::%make-unit
                        :metadata `(:identity (:host-metadata) :record-layouts
                                    ((:error-mapping (:missing-condition ,host))))
                        :source '((defun native-entry () nil)))
                       (snowgrave::%make-unit
                        :metadata '(:identity (:host-quote))
                        :source `((defun native-entry () ',(vector host))))))
      (let ((out (make-string-output-stream)))
        (check (handler-case
                   (progn (snowgrave:write-mezzano-unit-source unit out) nil)
                 (snowgrave:unsupported-definition (condition)
                   (eq (snowgrave:error-feature condition) :native-host-package))))
        (check (string= "" (get-output-stream-string out))))))
  ;; Exercise the reported path with actual adapter-produced record metadata.
  (let* ((entry 'native-reader-entry)
         (unit (snowgrave:close-source-unit
                (list :forms `((defclass native-reader-record () ()) (defun ,entry () nil)))
                :unit-name '(:native-reader-record) :closed-classes '(native-reader-record)
                :universe '(native-reader-record) :entries (list entry)
                :external-domains (list (list entry nil))))
         (out (make-string-output-stream)))
    (signals snowgrave:unsupported-definition (snowgrave:write-mezzano-unit-source unit out))
    (check (string= "" (get-output-stream-string out))))
  t)
