(defpackage #:snowgrave.macro-normalization.fixture
  (:use #:cl)
  (:shadowing-import-from #:snowgrave #:defclass #:defgeneric #:defmethod))

(in-package #:snowgrave.tests)

(defun macro-normalization-forms ()
  (let ((*package* (find-package :snowgrave.macro-normalization.fixture)))
    (read-from-string
     "((defclass cell () ((payload :initarg :payload)))
       (defparameter *trace* nil)
       (defgeneric score (object))
       (defmethod score ((object cell))
         (values (slot-value object 'payload) :score))
       (defgeneric relay (object))
       (defmethod relay ((object cell))
         (let ((callback (load-time-value #'score)))
           (loop repeat 3 collect (funcall callback object))))
       (defun boot (n) (make-instance 'cell :payload n))
       (defun method-loop (object) (relay object))
       (defun capture-loop (object)
         (loop repeat 2 collect
           (funcall (load-time-value #'score) object)))
       (defun lexical-macro (object)
         (macrolet ((closed-call (value) `(score ,value)))
           (macrolet ((twice (value &environment environment)
                        `(+ ,(macroexpand `(closed-call ,value) environment)
                            ,(macroexpand `(closed-call ,value) environment))))
             (twice object))))
       (defun macro-capture-loop (object)
         (macrolet ((closed-target () '(load-time-value #'score)))
           (loop repeat 2 collect (funcall (closed-target) object))))
       (defun symbol-macro-loop (object)
         (symbol-macrolet ((current object))
           (loop repeat 2 collect (score current))))
       (defun symbol-place (object)
         (symbol-macrolet ((payload (slot-value object 'payload)))
           (setf payload (+ payload 2))
           payload))
       (defun variable-shadow (object)
         (declare (ignore object))
         (symbol-macrolet ((value (error \"Shadowed symbol macro expanded.\")))
           (let ((value 31)) value)))
       (defun lambda-shadow (object)
         (symbol-macrolet ((argument (error \"Shadowed lambda argument expanded.\")))
           (funcall (lambda (argument) (score argument)) object)))
       (defun function-shadow (object)
         (macrolet ((choose (value) `(score ,value)))
           (flet ((choose (value) (declare (ignore value)) 37))
             (loop repeat 2 collect (choose object)))))
       (defun flet-definition-scope (object)
         (macrolet ((choose () '(score object)))
           (flet ((choose () (choose)))
             (loop repeat 2 collect (choose)))))
       (defun generic-shadow (object)
         (flet ((score (value) (declare (ignore value)) 41))
           (loop repeat 2 collect (score object))))
       (defun macro-shadow (object)
         (macrolet ((score (value) (declare (ignore value)) 43))
           (loop repeat 2 collect (score object))))
       (defun macro-lexical-capture (object)
         (flet ((score (value) (declare (ignore value)) 47))
           (macrolet ((target () '(function score)))
             (loop repeat 2 collect (funcall (target) object)))))
       (defun macro-null-environment-capture (object)
         (flet ((score (value) (declare (ignore value)) 51))
           (macrolet ((target () '(load-time-value #'score)))
             (loop repeat 2 collect (funcall (target) object)))))
       (defun ordinary-score (object)
         (values (+ 100 (slot-value object 'payload)) :ordinary))
       (defun macro-helper-capture (object)
         (flet ((score (value) (declare (ignore value)) 53))
           (macrolet ((target () '(function ordinary-score)))
             (loop repeat 2 collect (funcall (target) object)))))
       (defun cleanup-exit (object)
         (let ((*trace* nil))
           (multiple-value-bind (value tag)
               (block done
                 (unwind-protect
                     (loop repeat 3 do
                       (push :visit *trace*)
                       (return-from done
                         (values (funcall (load-time-value #'score) object) :escaped)))
                   (push :cleanup *trace*)))
             (values value tag (reverse *trace*)))))
       (defun named-exit (object)
         (loop named done for index from 0 below 4 do
           (when (= index 2)
             (return-from done (values (score object) :named)))
           finally (return-from done :wrong-exit)))
       (defun implicit-exit (object)
         (unwind-protect
             (loop repeat 2 do
               (return-from implicit-exit (values (score object) :implicit)))
           (score object)))
       (defun quoted-syntax (object)
         (declare (ignore object))
         '(loop for item in (:a :b) collect item)))")))

(defun macro-normalization-close (forms identity entries)
  (let ((*package* (find-package :snowgrave.macro-normalization.fixture)))
    (snowgrave:close-source-unit
     (list :forms forms) :unit-name identity
     :closed-classes (list (intern "CELL")) :universe (list (intern "CELL") 'number)
     :closed-generics
     (mapcar #'second
             (remove-if-not (lambda (form)
                              (eq (snowgrave:source-defining-kind form) :generic)) forms))
     :entries entries
     :external-domains
     (mapcar (lambda (entry)
               (list entry (list (if (string= (symbol-name entry) "BOOT")
                                    'number (intern "CELL")))))
             entries))))

(defun macro-normalization-fresh-test (unit expected)
  "Execute the emitted artifact with only Snowgrave's runtime in a fresh host."
  (let* ((root (asdf:system-source-directory "snowgrave"))
         (source (merge-pathnames ".build/macro-normalization-source.lisp" root))
         (metadata (merge-pathnames ".build/macro-normalization.metadata" root))
         (observations (merge-pathnames ".build/macro-normalization.expected" root))
         (driver (merge-pathnames ".build/macro-normalization-driver.lisp" root)))
    (ensure-directories-exist source)
    (with-open-file (stream source :direction :output :if-exists :supersede)
      (snowgrave:write-unit-source unit stream))
    (with-open-file (stream metadata :direction :output :if-exists :supersede)
      (snowgrave:write-unit-metadata unit stream))
    (with-open-file (stream observations :direction :output :if-exists :supersede)
      (with-standard-io-syntax
        (let ((*package* (find-package :cl-user)))
          (write expected :stream stream :readably t))))
    (with-open-file (stream driver :direction :output :if-exists :supersede)
      (dolist (form
               `((require :asdf)
                 (make-package "SNOWGRAVE.TESTS" :use '("COMMON-LISP"))
                 (asdf:initialize-source-registry
                  '(:source-registry (:directory ,root) :ignore-inherited-configuration))
                 (asdf:initialize-output-translations
                  '(:output-translations
                    (t ,(merge-pathnames ".build/fresh-macro-normalization-fasl/" root))
                    :ignore-inherited-configuration))
                 (asdf:load-system "snowgrave")
                 (load ,(merge-pathnames "scripts/artifact-functions.lisp" root))
                 (assert (not (find-package "SNOWGRAVE.MACRO-NORMALIZATION.FIXTURE")))
                 (multiple-value-bind (artifact warnings failure)
                     (compile-file ,source
                       :output-file ,(merge-pathnames ".build/macro-normalization.fasl" root))
                   (declare (ignore warnings))
                   (assert (not failure))
                   (load artifact))
                 (let* ((package (find-package "SNOWGRAVE.MACRO-NORMALIZATION.FIXTURE"))
                        (metadata (with-open-file (stream ,metadata) (read stream)))
                        (expected (with-open-file (stream ,observations) (read stream)))
                        (boot (uiop:symbol-call :snowgrave.artifact-tests :artifact-function
                                               metadata "BOOT")))
                   (assert (not (find-class (find-symbol "CELL" package) nil)))
                   (dolist (name '("SCORE" "RELAY" "METHOD-LOOP" "CAPTURE-LOOP"))
                     (assert (not (fboundp (find-symbol name package)))))
                   (dolist (case expected)
                     (destructuring-bind (name n values) case
                       (let ((function (uiop:symbol-call :snowgrave.artifact-tests :artifact-function
                                                        metadata name)))
                         (assert (equal values
                                        (multiple-value-list
                                         (funcall function (funcall boot n)))))))))
                 (assert (not (fboundp (find-symbol "CLOSE-SOURCE" "SNOWGRAVE.SBCL"))))
                 (format t "Fresh macro normalization executed.~%")))
        (write form :stream stream :readably t)
        (terpri stream)))
    (check (search "Fresh macro normalization executed."
                   (uiop:run-program
                    (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                          (namestring driver))
                    :output :string)))))

(defun macro-normalization-source-key-tests ()
  ;; Every trial expands a fresh GENSYM. Diagnostics must retain the authored
  ;; method's stable source position rather than any generated subform identity.
  (let* ((*package* (find-package :snowgrave.macro-normalization.fixture))
         (forms (read-from-string
                 "((defclass cell () ())
                   (defgeneric score (object))
                   (defmethod score ((object cell))
                     (macrolet ((bad-call (value)
                                  (let ((temporary (gensym \"LOCAL-\")))
                                    `(let ((,temporary ,value))
                                       (missing-operation ,temporary)))))
                       (loop repeat 1 do (bad-call object))))
                   (defgeneric relay (object))
                   (defmethod relay ((object cell)) (score object))
                   (defun entry (object) (relay object)))"))
         (identity '(macro-normalization-source-key :version 1))
         (entry (intern "ENTRY")))
    (dotimes (attempt 2)
      (declare (ignore attempt))
      (let ((condition
              (handler-case
                  (macro-normalization-close forms identity (list entry))
                (snowgrave:snowgrave-error (condition) condition))))
        (check (typep condition 'snowgrave:unclosed-call))
        (check (equal (snowgrave:error-source-key condition) (list identity 3)))
        (check (eq (snowgrave:error-feature condition) :call-target))
        (check (search "MISSING-OPERATION"
                       (string-upcase (snowgrave:error-detail condition))))))))

(defun macro-normalization-helper-tests ()
  ;; An implementation package name is not a proof that an expanded helper is
  ;; independent of the closed world. In particular, process creation remains
  ;; an undeclared external operation; this test must reject before executing it.
  (let* ((*package* (find-package :snowgrave.macro-normalization.fixture))
         (forms (read-from-string
                 "((defun entry ()
                     (macrolet ((unsafe-helper ()
                                  '(sb-ext:run-program \"must-never-execute\" nil)))
                       (loop repeat 1 do (unsafe-helper)))))"))
         (identity '(macro-normalization-helper :version 1))
         (condition
           (handler-case
               (snowgrave:close-source-unit
                (list :forms forms) :unit-name identity
                :entries (list (intern "ENTRY"))
                :external-domains (list (list (intern "ENTRY") nil)))
             (snowgrave:snowgrave-error (condition) condition))))
    (check (typep condition 'snowgrave:unclosed-call))
    (check (eq (snowgrave:error-feature condition) :call-target))
    (check (search "RUN-PROGRAM" (string-upcase (snowgrave:error-detail condition))))
    (check (equal (snowgrave:error-source-key condition) (list identity 1)))))

(defun macro-normalization-mutation-tests ()
  ;; A lexical callee changes across the back edge. A sound closer either
  ;; proves that change and returns ALTERNATE's values, or explicitly refuses
  ;; the missing mutable-callee proof. Retaining SCORE's old fact is unsound.
  (let* ((*package* (find-package :snowgrave.macro-normalization.fixture))
         (forms (read-from-string
                 "((defclass cell () ())
                   (defgeneric score (object))
                   (defmethod score ((object cell)) (values 7 :original))
                   (defun alternate (object)
                     (declare (ignore object)) (values 59 :changed))
                   (defun entry (object)
                     (let ((callback #'score))
                       (loop repeat 2 do (setq callback #'alternate))
                       (funcall callback object)))
                   (defun boot (n) (declare (ignore n)) (make-instance 'cell)))"))
         (identity '(macro-normalization-mutation :version 1))
         (unit nil)
         (condition
           (handler-case
               (progn
                 (setf unit
                       (snowgrave:close-source-unit
                        (list :forms forms) :unit-name identity
                        :closed-classes (list (intern "CELL"))
                        :universe (list (intern "CELL") 'number)
                        :closed-generics (list (intern "SCORE"))
                        :entries (mapcar #'intern '("ENTRY" "BOOT"))
                        :external-domains (read-from-string "((entry (cell)) (boot (number)))")))
                 nil)
             (snowgrave:snowgrave-error (condition) condition))))
    (if condition
        (progn
          (check (member (snowgrave:error-feature condition)
                         '(:value-domain-mutation :computed-function :internal-call-domain)))
          (check (equal (snowgrave:error-source-key condition) (list identity 5))))
        (let ((record (funcall (snowgrave:unit-function unit "BOOT") 0)))
          (check (equal (multiple-value-list
                         (funcall (snowgrave:unit-function unit "ENTRY") record))
                        '(59 :changed)))))))

(defun macro-normalization-vector-tests ()
  ;; The element variable has no authored type declaration. Admission must
  ;; derive only the facts the host vector iteration actually establishes.
  (let* ((*package* (find-package :snowgrave.macro-normalization.fixture))
         (forms (read-from-string
                 "((defun across-values (items)
                     (loop for item across items collect item)))"))
         (entry (intern "ACROSS-VALUES"))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(macro-vector :version 1)
                :universe '(vector) :entries (list entry)
                :external-domains (list (list entry '(vector))))))
    (dolist (form forms) (eval form))
    (dolist (input (list #(1 :two nil -3) "ab" #()))
      (check (equal (funcall entry input)
                    (funcall (snowgrave:unit-function unit entry) input))))))

(defun macro-normalization-mutable-scope-tests ()
  ;; The type guard precedes each write. Neither the guard nor a LET binding
  ;; established before an initializer may recreate a stale object/callee fact.
  (let* ((*package* (find-package :snowgrave.macro-normalization.fixture))
         (prefix (read-from-string
                  "((defclass cell () ((payload :initarg :payload)))
                    (defgeneric score (object))
                    (defmethod score ((object cell))
                      (values (slot-value object 'payload) :original))
                    (defmethod score ((object number))
                      (declare (ignore object)) (values 59 :changed))
                    (defun alternate (object)
                      (declare (ignore object)) (values 67 :alternate))
                    (defun boot (n) (make-instance 'cell :payload n)))"))
         (entry (intern "ENTRY"))
         (boot (intern "BOOT"))
         (cell (intern "CELL"))
         (score (intern "SCORE"))
         (bodies
           '("(if (typep object 'cell)
                  (progn (when flag (setq object 17)) (score object))
                  :outside)"
             "(if (typep object 'cell)
                  (let ((ignored (when flag (setq object 17))))
                    (declare (ignore ignored)) (score object))
                  :outside)"
             "(let ((callback #'score))
                (if (typep object 'cell)
                    (progn (when flag (setq callback #'alternate))
                           (funcall callback object))
                    :outside))"
             "(let ((callback #'score))
                (if (typep object 'cell)
                    (let ((ignored (when flag (setq callback #'alternate))))
                      (declare (ignore ignored)) (funcall callback object))
                    :outside))")))
    (loop for body in bodies for index from 1 do
      (let* ((forms (append prefix
                            (list (read-from-string
                                   (format nil "(defun entry (object flag) ~A)" body)))))
             (identity (list 'macro-mutable-scope :case index))
             (unit nil)
             (expected nil))
        (dolist (form forms) (eval form))
        (dolist (flag '(nil t))
          (push (list flag (multiple-value-list (funcall entry (funcall boot 7) flag))) expected))
        (let ((condition
                (handler-case
                    (progn
                      (setf unit
                            (snowgrave:close-source-unit
                             (list :forms forms) :unit-name identity
                             :closed-classes (list cell) :universe (list cell 'number 'symbol)
                             :closed-generics (list score) :entries (list boot entry)
                             :external-domains (list (list boot '(number))
                                                     (list entry (list cell 'symbol)))))
                      nil)
                  (snowgrave:snowgrave-error (condition) condition))))
          (if condition
              (progn
                (check (member (snowgrave:error-feature condition)
                               '(:value-domain-mutation :computed-function :internal-call-domain)))
                (check (equal (snowgrave:error-source-key condition) (list identity 7))))
              (dolist (case expected)
                (destructuring-bind (flag values) case
                  (check (equal values
                                (multiple-value-list
                                 (funcall (snowgrave:unit-function unit entry)
                                          (funcall (snowgrave:unit-function unit boot) 7) flag))))))))))))

(defun macro-normalization-tests ()
  (let* ((*package* (find-package :snowgrave.macro-normalization.fixture))
         (forms (macro-normalization-forms))
         (entries (mapcar #'second (remove-if-not (lambda (form) (eq (car form) 'defun)) forms)))
         (unit (macro-normalization-close forms '(macro-normalization :version 1) entries))
         (cases (remove "BOOT" entries :key #'symbol-name :test #'string=))
         (expected nil))
    (check (eq (getf (snowgrave:unit-report unit) :claim) :semantically-closed))
    (dolist (form forms) (eval form))
    (dolist (n '(7 -3))
      (dolist (entry cases)
        (let ((values (multiple-value-list (funcall entry (funcall (intern "BOOT") n)))))
          (push (list (symbol-name entry) n values) expected))))
    ;; Host definitions remain ordinary CLOS controls. Replacing their function
    ;; cells makes a leaked authored call fail immediately in closed execution.
    (let* ((score (intern "SCORE")) (relay (intern "RELAY"))
           (old-score (fdefinition score)) (old-relay (fdefinition relay)))
      (unwind-protect
           (progn
             (setf (fdefinition score) (lambda (&rest arguments)
                                       (declare (ignore arguments)) (error "Open SCORE leaked."))
                   (fdefinition relay) (lambda (&rest arguments)
                                       (declare (ignore arguments)) (error "Open RELAY leaked.")))
             (dolist (case expected)
               (destructuring-bind (name n values) case
                 (let ((record (funcall (snowgrave:unit-function unit "BOOT") n)))
                   (check (equal values
                                 (multiple-value-list
                                  (funcall (snowgrave:unit-function unit name) record))))))))
        (setf (fdefinition score) old-score (fdefinition relay) old-relay)))
    (macro-normalization-fresh-test unit (nreverse expected)))
  (macro-normalization-source-key-tests)
  (macro-normalization-helper-tests)
  (macro-normalization-mutation-tests)
  (macro-normalization-vector-tests)
  (macro-normalization-mutable-scope-tests))
