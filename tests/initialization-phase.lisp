(in-package #:snowgrave.tests)

(defun initialization-phase-source-check (unit)
  (let ((source (with-output-to-string (stream) (snowgrave:write-unit-source unit stream)))
        (metadata (prin1-to-string (snowgrave:unit-metadata unit))))
    (dolist (text (list source metadata))
      (check (not (search ":INITIALIZING-RECORD" text)))
      (check (not (search ":RECORD-VIEW-CLASSES" text)))
      (check (not (search "INITIALIZING-RECEIVER" text))))))

(defun initialization-phase-case (tag definitions body &key refusal fresh)
  (constructor-state-case
   tag definitions body '(t) :protocol t :refusal refusal
   :unit-check (lambda (unit)
                 (initialization-phase-source-check unit)
                 (when fresh (initialization-phase-fresh-test unit)))))

(defun initialization-phase-tests ()
  (initialization-phase-case :phase-after-stock
    "((defclass node () ((data :initform 17)))
       (defmethod initialize-instance :after ((n node) &rest args)
         (declare (ignore args)) (snowgrave.tests::constructor-state-event (eql (slot-value n 'data) 17))))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)" :fresh t)
  (initialization-phase-case :phase-receiver-alias
    "((defclass node () ((data :initform 17)))
       (defmethod initialize-instance :after ((n node) &rest args)
         (declare (ignore args)) (let ((alias n))
           (snowgrave.tests::constructor-state-event (eql (slot-value alias 'data) 17)))))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)")
  (initialization-phase-case :phase-shared-restores-unbound
    "((defclass node () ((data :initform 17)))
       (defmethod shared-initialize :before ((n node) names &rest args)
         (declare (ignore names args)) (slot-makunbound n 'data))
       (defmethod initialize-instance :after ((n node) &rest args)
         (declare (ignore args)) (snowgrave.tests::constructor-state-event (eql (slot-value n 'data) 17))))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)")
  (initialization-phase-case :phase-nested-receiver
    "((defclass node () ((data :initform 17)))
       (defmethod initialize-instance :around ((n node) &key (childp t) &allow-other-keys)
         (let ((alias n))
           (when childp (make-instance 'node :childp nil)
             (snowgrave.tests::constructor-state-event (slot-boundp alias 'data)))
           (multiple-value-prog1 (call-next-method)
             (snowgrave.tests::constructor-state-event (eql (slot-value alias 'data) 17))))))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)")
  (initialization-phase-case :phase-parent-activation-escape
    "((defclass node () ((data :initform 17) (parent :initarg :parent)))
       (defmethod initialize-instance :around ((n node) &key (childp t) &allow-other-keys)
         (when childp (make-instance 'node :childp nil :parent n)) (call-next-method)))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)" :refusal :initialization-activation-escape)
  (initialization-phase-case :phase-later-subclass
    "((defclass node () ((data :initform 17))) (defclass leaf (node) ())
       (defmethod initialize-instance :after ((n node) &rest args)
         (declare (ignore args)) (snowgrave.tests::constructor-state-event (eql (slot-value n 'data) 17)))
       (defmethod initialize-instance :after ((n leaf) &rest args)
         (declare (ignore args)) (setf (slot-value n 'data) 41)
         (snowgrave.tests::constructor-state-event (eql (slot-value n 'data) 41))))"
    "(declare (ignore root)) (typep (make-instance 'leaf) 'leaf)")
  (initialization-phase-case :phase-alias-before-next
    "((defclass node () ((data :initform 17)))
       (defmethod initialize-instance :around ((n node) &rest args)
         (declare (ignore args)) (let ((alias n))
           (multiple-value-prog1 (call-next-method)
             (snowgrave.tests::constructor-state-event (eql (slot-value alias 'data) 17))))))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)")
  (initialization-phase-case :phase-next-method-p
    "((defclass node () ((data :initform 17)))
       (defmethod initialize-instance :around ((n node) &rest args)
         (declare (ignore n args)) (snowgrave.tests::constructor-state-event (next-method-p))
         (call-next-method)))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)")
  (initialization-phase-case :phase-write-before-next
    "((defclass node () ((data :initform 41)))
       (defmethod initialize-instance :around ((n node) &rest args)
         (declare (ignore args)) (setf (slot-value n 'data) 17)
         (multiple-value-prog1 (call-next-method)
           (snowgrave.tests::constructor-state-event (eql (slot-value n 'data) 17)))))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)")
  (initialization-phase-case :phase-boundp-guard
    "((defclass node () ((data)))
       (defmethod initialize-instance :after ((n node) &rest args)
         (declare (ignore args)) (unless (slot-boundp n 'data) (setf (slot-value n 'data) 17))
         (snowgrave.tests::constructor-state-event (integerp (slot-value n 'data)))))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)")
  (initialization-phase-case :phase-sequential-setf
    "((defclass node () ((data) (copy)))
       (defmethod initialize-instance :after ((n node) &rest args)
         (declare (ignore args)) (setf (slot-value n 'data) 17 (slot-value n 'copy) (slot-value n 'data))
         (snowgrave.tests::constructor-state-event (eql (slot-value n 'copy) 17))))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)")
  (initialization-phase-case :phase-alignment-guard
    "((defclass node () ((data :initarg :data :initform 8)))
       (defmethod initialize-instance :after ((n node) &rest args)
         (declare (ignore args))
         (unless (and (integerp (slot-value n 'data)) (plusp (slot-value n 'data))
                      (zerop (logand (slot-value n 'data) (1- (slot-value n 'data)))))
           (error \"Bad alignment\"))
         (snowgrave.tests::constructor-state-event (eql (slot-value n 'data) 16))))"
    "(declare (ignore root)) (typep (make-instance 'node :data 16) 'node)")
  (initialization-phase-case :phase-aux-write
    "((defclass node () ((data)))
       (defmethod initialize-instance :after ((n node) &rest args &aux (ignored (setf (slot-value n 'data) 17)))
         (declare (ignore args ignored)) (snowgrave.tests::constructor-state-event (eql (slot-value n 'data) 17))))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)")
  (initialization-phase-case :phase-supplied-key-skips-write
    "((defclass node () ((data)))
       (defmethod initialize-instance :around ((n node) &key (flag (progn (setf (slot-value n 'data) 17) nil)))
         (declare (ignore flag)) (slot-value n 'data) (call-next-method)))"
    "(declare (ignore root)) (typep (make-instance 'node :flag t) 'node)" :refusal :graph-state-slot-read)
  (initialization-phase-case :phase-supplied-key-skips-next
    "((defclass node () ((data :initform 17)))
       (defmethod initialize-instance :around ((n node) &key (flag (call-next-method)))
         (declare (ignore flag)) (slot-value n 'data) n))"
    "(declare (ignore root)) (typep (make-instance 'node :flag t) 'node)" :refusal :graph-state-slot-read)
  (initialization-phase-case :phase-let-value-point
    "((defclass node () ((data) (copy)))
       (defmethod initialize-instance :around ((n node) &rest args)
         (declare (ignore args)) (setf (slot-value n 'data) 17)
         (let ((x (progn (setf (slot-value n 'data) (vector 0)) (slot-value n 'data))))
           (when (typep x 'integer) (setf (slot-value n 'copy) 17)))
         (slot-value n 'copy) (call-next-method)))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)" :refusal t)
  (initialization-phase-case :phase-helper-call-positive
    "((defclass node () ((data))) (defun zap (n ignored) (declare (ignore ignored)) (slot-makunbound n 'data) 7)
       (defmethod initialize-instance :after ((n node) &rest args)
         (declare (ignore args)) (zap n (progn (setf (slot-value n 'data) 17) nil))))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)")
  (initialization-phase-case :phase-helper-post-argument-effects
    "((defclass node () ((data))) (defun zap (n ignored) (declare (ignore ignored)) (slot-makunbound n 'data) 7)
       (defmethod initialize-instance :after ((n node) &rest args)
         (declare (ignore args)) (zap n (progn (setf (slot-value n 'data) 17) nil)) (slot-value n 'data)))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)" :refusal :graph-state-slot-read)
  (initialization-phase-case :phase-native-results-after-effects
    "((defclass node () ((data :initform 17)))
       (defun clear-and-values (n) (slot-makunbound n 'data) (values 17 :ok))
       (defmethod initialize-instance :after ((n node) &rest args)
         (declare (ignore args))
         (multiple-value-bind (value status) (clear-and-values n)
           (snowgrave.tests::constructor-state-event value)
           (snowgrave.tests::constructor-state-event (eq status :ok)))
         (snowgrave.tests::constructor-state-event (eql (clear-and-values n) 17))
         (snowgrave.tests::constructor-state-event (slot-boundp n 'data))))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)")
  (initialization-phase-case :phase-private-result-after-effects
    "((defclass node () ((data :initform 17)))
       (defun clear-and-return (n) (slot-makunbound n 'data) n)
       (defmethod initialize-instance :after ((n node) &rest args)
         (declare (ignore args)) (snowgrave.tests::constructor-state-event (clear-and-return n))))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)" :refusal :graph-state-external-argument)
  (initialization-phase-case :phase-before-read
    "((defclass node () ((data :initform 17)))
       (defmethod initialize-instance :before ((n node) &rest args)
         (declare (ignore args)) (slot-value n 'data)))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)" :refusal :graph-state-slot-read)
  (initialization-phase-case :phase-skipped-shared
    "((defclass node () ((data :initform 17)))
       (defmethod shared-initialize :around ((n node) names &rest args) (declare (ignore names args)) n)
       (defmethod initialize-instance :after ((n node) &rest args) (declare (ignore args)) (slot-value n 'data)))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)" :refusal :graph-state-slot-read)
  (initialization-phase-case :phase-alias-unbind
    "((defclass node () ((data :initform 17)))
       (defmethod initialize-instance :around ((n node) &rest args)
         (declare (ignore args)) (let ((alias n))
           (call-next-method) (slot-makunbound alias 'data) (slot-value n 'data))))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)" :refusal :graph-state-slot-read)
  (initialization-phase-case :phase-dead-tail
    "((defclass node () ((data :initform 17))) (defclass child (node) ())
       (defmethod initialize-instance :around ((n node) &rest args)
         (declare (ignore args)) (return-from initialize-instance n)
         (setf (slot-value n 'data) 17) (call-next-method))
       (defmethod initialize-instance :around ((n child) &rest args)
         (declare (ignore args)) (call-next-method) (integerp (slot-value n 'data))))"
    "(declare (ignore root)) (typep (make-instance 'child) 'child)" :refusal :graph-state-slot-read)
  (initialization-phase-sharing-tests))

(defun count-source-occurrences (needle source)
  (loop for position = (search needle source) then (search needle source :start2 (+ position (length needle)))
        while position count position))

(defun initialization-phase-sharing-tests ()
  ;; Each layer invokes the same continuation twice. Runtime effects double,
  ;; but the emitted leaf body is retained once per actual concrete class cell.
  (dolist (depth '(1 3 6))
    (let ((definitions
            (with-output-to-string (stream)
              (write-string "((defclass node () ((data :initform 17)))" stream)
              (write-string "(defmethod initialize-instance :after ((n node) &rest args)
                                (declare (ignore n args))
                                (snowgrave.tests::constructor-state-event :phase-leaf-effect))" stream)
              (loop for index from 1 to depth
                    for parent = (if (= index 1) "node" (format nil "layer~D" (1- index)))
                    do (format stream "(defclass layer~D (~A) ())
                         (defmethod initialize-instance :around ((n layer~D) &rest args)
                           (declare (ignore n args)) (call-next-method) (call-next-method))"
                               index parent index))
              (write-char #\) stream))))
      (constructor-state-case
       (list :phase-sharing depth) definitions
       (format nil "(declare (ignore root)) (typep (make-instance 'layer~D) 'layer~D)" depth depth) '(t)
       :protocol t :unit-check
       (lambda (unit)
         (initialization-phase-source-check unit)
         (let ((source (with-output-to-string (stream) (snowgrave:write-unit-source unit stream))))
           (check (<= (count-source-occurrences ":PHASE-LEAF-EFFECT" source) (1+ depth)))))))))


(defun initialization-phase-fresh-test (unit)
  ;; Both modes load only the runtime and the ordinary artifact. No authored
  ;; class or closer is available to supply phase facts during execution.
  (let* ((root (asdf:system-source-directory "snowgrave"))
         (cache (merge-pathnames "snowgrave-initialization-fresh/" (uiop:temporary-directory))))
    (uiop:with-temporary-file (:pathname source :stream source-stream :type "lisp")
      (snowgrave:write-unit-source unit source-stream) (finish-output source-stream)
      (uiop:with-temporary-file (:pathname data :stream data-stream :type "metadata")
        (snowgrave:write-unit-metadata unit data-stream) (finish-output data-stream)
        (uiop:with-temporary-file (:pathname driver :stream driver-stream :type "lisp")
          (let ((fasl (compile-file-pathname source)))
            (unwind-protect
                 (progn
                   (dolist (form
                            `((require :asdf)
                              (make-package "SNOWGRAVE.TESTS" :use '("COMMON-LISP"))
                              (defvar snowgrave.tests::*constructor-state-events* nil)
                              (defun snowgrave.tests::constructor-state-event (tag)
                                (push tag snowgrave.tests::*constructor-state-events*) nil)
                              (asdf:initialize-source-registry
                               '(:source-registry (:directory ,root) :ignore-inherited-configuration))
                              (asdf:initialize-output-translations
                               '(:output-translations (t ,cache) :ignore-inherited-configuration))
                              (asdf:load-system "snowgrave")
                              (if (string= (first (uiop:command-line-arguments)) "source")
                                  (load ,source)
                                  (multiple-value-bind (artifact warnings failure)
                                      (compile-file ,source :output-file ,fasl)
                                    (declare (ignore warnings)) (assert (not failure)) (load artifact)))
                              (let* ((metadata (with-open-file (in ,data) (read in)))
                                     (entry (find "ENTRY" (getf metadata :entries) :test #'string=
                                                  :key (lambda (row) (symbol-name (getf row :name)))))
                                     (key (getf entry :bound-code-key))
                                     (function (fdefinition (find-symbol (second key) (first key)))))
                                (assert (equal '(t) (multiple-value-list (funcall function))))
                                (assert (equal '(t) snowgrave.tests::*constructor-state-events*))
                                (assert (not (fboundp (getf entry :name))))
                                (dolist (layout (getf metadata :record-layouts))
                                  (assert (not (find-class (getf layout :class) nil)))))
                              (assert (not (let ((package (find-package "SNOWGRAVE.SBCL")))
                                             (and package (let ((name (find-symbol "CLOSE-SOURCE" package)))
                                                            (and name (fboundp name)))))))
                              (format t "Fresh initialization phase checked.~%")))
                     (let ((*package* (find-package :cl-user)))
                       (write form :stream driver-stream :readably t) (terpri driver-stream)))
                   (finish-output driver-stream)
                   (dolist (mode '("source" "fasl"))
                     (check (search "Fresh initialization phase checked."
                                    (uiop:run-program (list "sbcl" "--no-sysinit" "--no-userinit" "--disable-debugger"
                                                            "--script" (namestring driver) mode)
                                                      :output :string :error-output *error-output*)))))
              (ignore-errors (delete-file fasl)))))))))
