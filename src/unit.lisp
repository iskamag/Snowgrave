(in-package #:snowgrave)

(defstruct (closed-unit (:constructor %make-unit (metadata source bindings)))
  metadata source bindings)

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

(defun body-parts (body)
  (let ((prefix nil))
    (when (and (stringp (first body)) (rest body)) (push (pop body) prefix))
    (loop while (and (consp (first body)) (eq (caar body) 'declare))
          do (push (pop body) prefix))
    (values (nreverse prefix) body)))

(defun entry-domain-test (build domain variable)
  (cond ((source-class-p build domain) (closed-class-test build domain variable))
        ((and (consp domain) (eq (first domain) 'eql))
         (unless (or (numberp (second domain)) (characterp (second domain)) (symbolp (second domain)))
           (unsupported build :configuration-input "Object identity capture is outside the source core."))
         `(eql ,variable ',(second domain)))
        (t `(typep ,variable ',domain))))

(defun emit-functions (build)
  (dolist (form (build-forms build))
    (when (eq (first form) 'defun)
      (destructuring-bind (operator name lambda-list &rest body) form
        (declare (ignore operator))
        (multiple-value-bind (prefix executable) (body-parts body)
          (let* ((entryp (member name (getf (build-declaration build) :entries) :test #'equal))
                 (domains (second (assoc name (getf (build-declaration build) :external-domains) :test #'equal)))
                 (checks
                   (when entryp
                     (unless (and (every #'symbolp lambda-list)
                                  (notany (lambda (x) (member x lambda-list-keywords)) lambda-list)
                                  (= (length lambda-list) (length domains)))
                       (unsupported build :entry-domain
                                    "Entry ~S needs required parameters and one declared domain per parameter." name))
                     (loop for variable in lambda-list for domain in domains
                           collect `(unless ,(entry-domain-test build domain variable)
                                       (error 'type-error :datum ,variable :expected-type ',domain)))))
                 (lambda-form
                   (rewrite-form build
                                 `(lambda ,lambda-list ,@prefix
                                     (block ,(if (consp name) (second name) name)
                                       ,@checks ,@executable))
                                 :closed)))
            (emit-form build (list* 'defun (closed-name build name) (rest lambda-form))))))))
  ;; Install globals only after all ordinary function definitions exist.
  (dolist (form (build-forms build))
    (when (member (first form) '(defvar defparameter defconstant))
      (emit-form build (list* (first form) (closed-name build (second form))
                             (when (cddr form)
                               (cons (rewrite-form build (third form) :closed) (cdddr form))))))))

(defun check-residual-source (build forms)
  "The final source must contain no builder symbols or live builder objects."
  (let ((seen (make-hash-table :test #'eq)))
    (labels ((visit (value)
               (cond ((symbolp value)
                      (when (eq (symbol-package value) (build-open-package build))
                        (unsupported build :builder-reference "Builder symbol remains: ~S." value)))
                     ((consp value)
                      (unless (gethash value seen)
                        (setf (gethash value seen) t) (visit (car value)) (visit (cdr value))))
                     ((or (numberp value) (characterp value) (stringp value)) nil)
                     ((simple-vector-p value) (map nil #'visit value))
                     (t (unsupported build :builder-object "Non-source object remains: ~S." (type-of value))))))
      (visit forms))))

(defun package-bootstrap-forms (forms)
  (let ((packages (make-hash-table :test #'equal)) (seen (make-hash-table :test #'eq)))
    (labels ((visit (value)
               (cond ((symbolp value)
                      (let ((package (symbol-package value)))
                        (when (and package (not (member (package-name package) '("COMMON-LISP" "KEYWORD") :test #'string=)))
                          (pushnew (symbol-name value) (gethash (package-name package) packages) :test #'string=))))
                     ((consp value)
                      (unless (gethash value seen)
                        (setf (gethash value seen) t) (visit (car value)) (visit (cdr value))))
                     ((simple-vector-p value) (map nil #'visit value)))))
      (visit forms))
    (let ((package-variable (gensym "PACKAGE")) (name-variable (gensym "NAME")))
     (loop for name in (sort (loop for name being the hash-keys of packages collect name) #'string<)
          collect
          ;; Exporting referenced names in newly created source packages also
          ;; makes original single-colon literal symbols readable on replay.
          `(eval-when (:compile-toplevel :load-toplevel :execute)
              (unless (find-package ,name)
                (let ((,package-variable (make-package ,name :use '("COMMON-LISP"))))
                  (dolist (,name-variable ',(sort (gethash name packages) #'string<))
                    (shadow ,name-variable ,package-variable)
                    (export (intern ,name-variable ,package-variable) ,package-variable)))))))))

(defun write-unit-source (unit stream)
  (let ((*package* (find-package :cl)) (*print-readably* t) (*print-circle* t) (*print-pretty* t))
    (write '(in-package #:common-lisp) :stream stream)
    (terpri stream)
    (dolist (form (package-bootstrap-forms (closed-unit-source unit)))
      (write form :stream stream) (terpri stream))
    (dolist (form (closed-unit-source unit))
      (write form :stream stream) (terpri stream))))
(defun write-unit-metadata (unit stream)
  (let ((*package* (find-package :cl)) (*print-readably* t) (*print-circle* t))
    (write (closed-unit-metadata unit) :stream stream) (terpri stream)))

(defun close-source-unit (source &rest declaration
                          &key unit-name entries closed-classes closed-generics universe
                            external-domains external-operations (domain-violation :signal) (adapter :sbcl)
                          &allow-other-keys)
  (declare (ignore closed-classes closed-generics universe external-domains external-operations))
  (loop for (key value) on declaration by #'cddr
        do (unless (member key '(:unit-name :entries :closed-classes :closed-generics :universe
                                 :external-domains :external-operations :domain-violation :adapter))
             (unsupported nil :declaration "Unsupported source-core option ~S = ~S." key value)))
  (unless (and unit-name entries (eq adapter :sbcl) (eq domain-violation :signal))
    (unsupported nil :declaration "A named unit, public entries, SBCL and :SIGNAL policy are required."))
  (let* ((number (incf *unit-sequence*))
         (open (make-package (format nil "SNOWGRAVE.BUILD.~D" number) :use '(:cl)))
         (output (make-package (format nil "SNOWGRAVE.CLOSED.~D" number) :use '(:cl)))
         (build (make-build :identity (copy-source-graph unit-name)
                            :declaration (copy-source-graph declaration)
                            :forms (read-source source) :open-package open :output-package output))
         (success nil))
    (setf (build-open-literal-name build) (intern "%LITERALS" open)
          (build-closed-literal-name build) (intern "%LITERALS" output))
    (unwind-protect
         (progn
           (index-source build)
           (loop for (key actual) in (list (list :closed-classes (build-classes build))
                                           (list :closed-generics (build-generics build)))
                 when (loop for tail on declaration by #'cddr thereis (eq (first tail) key))
                   do (let ((selected (getf declaration key)))
                        (unless (and (null (set-difference actual selected :test #'equal))
                                     (null (set-difference selected actual :test #'equal)))
                          (unsupported build :partial-cohort
                                       "~S must name the complete owned set ~S." key actual))))
           (dolist (entry entries)
             (unless (member entry (build-functions build) :test #'equal)
               (unsupported build :entry "Entry ~S needs an owned ordinary definition." entry)))
           ;; Unsupported construction metaprotocols must fail before installing
           ;; any methods on the host's standard initialization generics.
           (dolist (form (build-method-sources build))
             (when (member (second form) '(make-instance allocate-instance initialize-instance
                                          shared-initialize reinitialize-instance slot-missing slot-unbound))
               (unsupported build :custom-record-protocol
                            "Authored ~S needs a closed initialization realization." (second form))))
           (let* ((open-forms (mapcar (lambda (form) (open-definition build form)) (build-forms build)))
                  (literals (literal-definition build :open)))
             (when literals (eval literals))
             (dolist (form open-forms) (eval form)))
           (prepare-records build)
           (emit-records build)
           (emit-generics build)
           (emit-functions build)
           (let* ((literals (literal-definition build :closed))
                  (specials (loop for form in (build-forms build)
                                  when (member (first form) '(defvar defparameter))
                                    collect (closed-name build (second form))))
                  (forms (append (when specials (list (list 'declaim (cons 'special specials))))
                                 (when literals (list literals)) (nreverse (build-generated build))))
                  (metadata (list :identity (build-identity build) :mechanism :mop-two-pass :profile :source-core
                                  :classes (copy-list (build-classes build))
                                  :entries (mapcar (lambda (name)
                                                     (let ((symbol (closed-name build name)))
                                                       (list :name name :code-key
                                                             (list (package-name output) (symbol-name symbol)))))
                                                   entries))))
             (check-residual-source build forms)
             (dolist (form forms) (eval form))
             (let ((unit (%make-unit metadata forms
                                    (mapcar (lambda (name) (cons name (fdefinition (closed-name build name)))) entries))))
               (setf success t)
               unit)))
      (delete-package open)
      (unless success (delete-package output)))))
