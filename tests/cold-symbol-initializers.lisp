(defpackage #:snowgrave.cold-symbol.fixture (:use #:cl))
(defpackage #:snowgrave.cold-symbol.shadow (:use #:cl) (:shadow #:make-symbol))
(in-package #:snowgrave.tests)

(defvar *cold-symbol-sequence* 0)
(defun cold-symbol-forms (text)
  (let ((*package* (find-package :snowgrave.cold-symbol.fixture)))
    (read-from-string text)))

(defun close-cold-symbols (forms &key classes domains imports)
  (snowgrave:close-source-unit
   (list :forms forms) :unit-name (list :cold-symbols (incf *cold-symbol-sequence*))
   :closed-classes classes :universe classes
   :entries '(snowgrave.cold-symbol.fixture::entry)
   :external-domains (list (list 'snowgrave.cold-symbol.fixture::entry domains))
   :native-bindings imports))

(defun check-cold-symbol-observation (returned)
  (check (= 4 (length returned)))
  (check (eq (first returned) (second returned)))
  (check (not (eq (first returned) (third returned))))
  (let* ((nested (fourth returned))
         (symbols (list (first returned) (third returned) (aref nested 0) (car (aref nested 1)))))
    (check (= 4 (length (remove-duplicates symbols :test #'eq))))
    (dolist (symbol symbols)
      (check (symbolp symbol))
      (check (string= "MiXeD" (symbol-name symbol)))
      (check (not (symbol-package symbol)))
      (check (not (boundp symbol)))
      (check (not (fboundp symbol)))
      (check (null (symbol-plist symbol))))))

(defun cold-symbol-fresh-test (unit)
  (let* ((root (asdf:system-source-directory "snowgrave"))
         (cache (merge-pathnames "snowgrave-cold-symbol-fresh/" (uiop:temporary-directory))))
    (uiop:with-temporary-file (:pathname source :stream source-stream :type "lisp")
      (snowgrave:write-unit-source unit source-stream)
      (finish-output source-stream)
      (uiop:with-temporary-file (:pathname metadata :stream metadata-stream :type "metadata")
        (snowgrave:write-unit-metadata unit metadata-stream)
        (finish-output metadata-stream)
        (uiop:with-temporary-file (:pathname driver :stream driver-stream :type "lisp")
          (let ((fasl (make-pathname :type "fasl" :defaults source)))
            (unwind-protect
                 (progn
                   (dolist (form
                            `((require :asdf)
                              (make-package "SNOWGRAVE.TESTS" :use '("COMMON-LISP"))
                              (asdf:initialize-source-registry
                               '(:source-registry (:directory ,root) :ignore-inherited-configuration))
                              (asdf:initialize-output-translations
                               '(:output-translations (t ,cache) :ignore-inherited-configuration))
                              (asdf:load-system "snowgrave")
                              (load ,(merge-pathnames "scripts/artifact-functions.lisp" root))
                              (assert (not (find-package "SNOWGRAVE.COLD-SYMBOL.FIXTURE")))
                              (defun verify-symbols (metadata)
                                (let* ((entry (uiop:symbol-call :snowgrave.artifact-tests :artifact-function metadata "ENTRY"))
                                       (returned (multiple-value-list (funcall entry)))
                                       (nested (fourth returned))
                                       (symbols (list (first returned) (third returned)
                                                      (aref nested 0) (car (aref nested 1)))))
                                  (assert (= 4 (length returned)))
                                  (assert (eq (first returned) (second returned)))
                                  (assert (= 4 (length (remove-duplicates symbols :test #'eq))))
                                  (dolist (symbol symbols)
                                    (assert (and (symbolp symbol) (not (symbol-package symbol))
                                                 (string= "MiXeD" (symbol-name symbol))
                                                 (not (boundp symbol)) (not (fboundp symbol))
                                                 (null (symbol-plist symbol)))))
                                  (first returned)))
                              (load ,source)
                              (let* ((metadata (with-open-file (stream ,metadata) (read stream)))
                                     (old (verify-symbols metadata)))
                                ;; Every installation executes each recipe anew;
                                ;; entry calls themselves keep the installed identity.
                                (dolist (kind '(:source :fasl :fasl))
                                  (if (eq kind :source) (load ,source)
                                      (progn
                                        (unless (probe-file ,fasl)
                                          (multiple-value-bind (artifact warnings failure)
                                              (compile-file ,source :output-file ,fasl)
                                            (declare (ignore artifact warnings)) (assert (not failure))))
                                        (load ,fasl)))
                                  (let ((current (verify-symbols metadata)))
                                    (when old (assert (not (eq old current))))
                                    (assert (eq current (verify-symbols metadata)))
                                    (setf old current))))
                              (assert (not (fboundp 'snowgrave.sbcl:close-source)))
                              (format t "Fresh cold symbol recipes executed.~%")))
                     (write form :stream driver-stream :readably t) (terpri driver-stream))
                   (finish-output driver-stream)
                   (check (search "Fresh cold symbol recipes executed."
                                  (uiop:run-program
                                   (list "sbcl" "--no-sysinit" "--no-userinit" "--script" (namestring driver))
                                   :output :string :error-output *error-output*))))
              (when (probe-file fasl) (delete-file fasl)))))))))

(defun cold-symbol-refusal (forms feature position &key classes domains imports)
  (let ((condition (handler-case
                       (progn (close-cold-symbols forms :classes classes :domains domains :imports imports) nil)
                     (snowgrave:snowgrave-error (condition) condition))))
    (check (typep condition 'snowgrave:snowgrave-error))
    (when feature (check (eq feature (snowgrave:error-feature condition))))
    (when position (check (= position (second (snowgrave:error-source-key condition)))))
    condition))

(defun cold-symbol-initializer-tests ()
  (let* ((forms (cold-symbol-forms
                 "((defclass node () ())
                    (defparameter *left* (make-symbol \"MiXeD\"))
                    (defparameter *right* (make-symbol '\"MiXeD\"))
                    (defparameter *nested* (vector (make-symbol \"MiXeD\") (cons (make-symbol \"MiXeD\") nil)))
                    (defun entry () (values *left* *left* *right* *nested*)))"))
         (unit (close-cold-symbols forms :classes '(snowgrave.cold-symbol.fixture::node))))
    (check-cold-symbol-observation (multiple-value-list (funcall (snowgrave:unit-function unit 'snowgrave.cold-symbol.fixture::entry))))
    (dolist (form forms) (eval form))
    (check-cold-symbol-observation (multiple-value-list (snowgrave.cold-symbol.fixture::entry)))
    ;; The runtime entry has no MAKE-SYMBOL callable or allocation in its body.
    (check (not (member (snowgrave::function-name-key 'make-symbol)
                        (getf (snowgrave:unit-report unit) :dependencies) :test #'equal)))
    (cold-symbol-fresh-test unit))
  ;; DEFVAR's admitted initializer also establishes one installed identity;
  ;; calling the runtime entry does not execute the initializer again.
  (let* ((forms (cold-symbol-forms
                 "((defvar *kept* (make-symbol \"KEPT\")) (defun entry () *kept*))"))
         (unit (close-cold-symbols forms))
         (marker (funcall (snowgrave:unit-function unit 'snowgrave.cold-symbol.fixture::entry))))
    (check (string= "KEPT" (symbol-name marker)))
    (check (eq marker (funcall (snowgrave:unit-function unit 'snowgrave.cold-symbol.fixture::entry)))))
  ;; Invalid/dynamic names and unrelated calls never execute during admission.
  (dolist (initializer '("(make-symbol)" "(make-symbol \"x\" \"y\")" "(make-symbol 7)"
                         "(make-symbol nil)" "(make-symbol (get-universal-time))"
                         "(make-symbol (progn (error \"executed\") \"x\"))"
                         "(load-time-value (make-symbol \"x\"))"))
    (cold-symbol-refusal
     (cold-symbol-forms (format nil "((defparameter *bad* ~A) (defun entry () 7))" initializer))
     :global-initializer 1))
  (dolist (body '("(make-symbol \"x\")" "(funcall #'make-symbol \"x\")"))
    (cold-symbol-refusal (cold-symbol-forms (format nil "((defun entry () ~A))" body)) :call-target 1))
  (cold-symbol-refusal (cold-symbol-forms "((defun entry () (load-time-value (make-symbol \"x\"))))") :load-time-capture 1)
  (cold-symbol-refusal
   '((defun snowgrave.cold-symbol.shadow::make-symbol (name)
       (declare (ignore name)) (error "A same-named helper must not execute"))
     (defparameter snowgrave.cold-symbol.fixture::*bad*
       (snowgrave.cold-symbol.shadow::make-symbol "x"))
     (defun snowgrave.cold-symbol.fixture::entry () 7))
   :global-initializer 2)
  ;; No cross-global alias recipe or literal symbol capture is invented.
  (let ((name 'snowgrave.cold-symbol.fixture::*left*) (saved (make-symbol "ORIGINAL")))
    (setf (symbol-value name) saved)
    (cold-symbol-refusal
     (cold-symbol-forms "((defparameter *left* (make-symbol \"NEW\")) (defparameter *alias* *left*) (defun entry () 7))")
     :global-initializer 2)
    (check (eq saved (symbol-value name))))
  ;; Existing capture/import owners must refuse an old marker in installed
  ;; state; emitting a new equal-named symbol cannot preserve that relation.
  (dolist (nativep '(nil t))
    (let* ((forms (cold-symbol-forms
                   "((defparameter *marker* (make-symbol \"FREE-CELL\"))
                      (defclass holder () ((payload :initarg :payload)))
                      (defun entry (root) (eq (slot-value root 'payload) *marker*)))")))
      (dolist (form forms) (eval form))
      (let* ((marker (symbol-value 'snowgrave.cold-symbol.fixture::*marker*))
             (payload (if nativep (vector marker) marker))
             (root (make-instance 'snowgrave.cold-symbol.fixture::holder :payload payload))
             (condition (cold-symbol-refusal forms nil nil
                          :classes '(snowgrave.cold-symbol.fixture::holder)
                          :domains (list (list 'eql root))
                          :imports (when nativep (list (list :words payload))))))
        (check (typep condition 'snowgrave:unsupported-definition))
        (check (eq :graph-node-kind (snowgrave:error-feature condition)))
        (check (eq marker (symbol-value 'snowgrave.cold-symbol.fixture::*marker*)))
        (check (eq payload (slot-value root 'snowgrave.cold-symbol.fixture::payload)))
        (when nativep (check (eq marker (aref payload 0))))))))
