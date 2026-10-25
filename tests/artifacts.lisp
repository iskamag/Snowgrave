(in-package #:snowgrave.tests)

(defun fresh-artifact-test ()
  (multiple-value-bind (unit package)
      (make-fixture
       :artifact
       "((defclass cell () ((value :initarg :value :reader value)))
          (defgeneric next-value (object))
          (defmethod next-value ((object cell)) (+ 1 (value object)))
          (defun helper (object) (next-value object))
          (defun entry (n) (helper (make-instance 'cell :value n)))
          (defun literals ()
            (values (eq '#1=(1 2) '#1#) (eq '#1# '(1 2))
                    (eq #2=\"same\" '#2#) (eq #2# \"same\")
                    (eq #3=#(1 2) '#3#) (eq #3# #(1 2)))))"
       "(entry literals)" "((entry (number)) (literals ()))"
       "(value next-value)" :universe "(cell number)")
    (compare-entry unit package "ENTRY" '(41) '((42) nil))
    (compare-entry unit package "LITERALS" nil '((t nil t nil t nil) nil))
    (let* ((metadata (snowgrave:unit-metadata unit))
           (entry (find (find-symbol "ENTRY" package) (getf metadata :entries)
                        :key (lambda (row) (getf row :name))))
           (key (getf entry :code-key))
           (literal-key (getf (find (find-symbol "LITERALS" package) (getf metadata :entries)
                                   :key (lambda (row) (getf row :name))) :code-key))
           (directory (merge-pathnames
                       (format nil "snowgrave-core-artifact-~A-~D-~D/" (lisp-implementation-type) (get-universal-time) *fixture-sequence*)
                       (uiop:temporary-directory)))
           (source (merge-pathnames "unit.lisp" directory))
           (driver (merge-pathnames "run.lisp" directory)))
      (check (and (stringp (first key)) (stringp (second key))) "Missing artifact entry identity")
      (ensure-directories-exist source)
      (unwind-protect
           (progn
             (with-open-file (stream source :direction :output :if-exists :supersede)
               (snowgrave:write-unit-source unit stream))
             (dolist (mode '(:source :fasl))
               (with-open-file (stream driver :direction :output :if-exists :supersede)
                 (let ((*package* (find-package :cl)) (*print-readably* nil) (*print-circle* t)
                       (compiled-path (gensym "COMPILED-PATH"))
                       (warnings (gensym "WARNINGS")) (failure (gensym "FAILURE")))
                   (write `(progn
                             ,(if (eq mode :source)
                                  `(load ,(namestring source))
                                  `(multiple-value-bind (,compiled-path ,warnings ,failure)
                                       (compile-file ,(namestring source))
                                     (declare (ignore ,warnings))
                                     (assert (not ,failure))
                                     (load ,compiled-path)))
                             (assert (= 42 (funcall (fdefinition (find-symbol ,(second key) ,(first key))) 41)))
                             (assert (equal '(t nil t nil t nil)
                                            (multiple-value-list
                                             (funcall (fdefinition
                                                       (find-symbol ,(second literal-key) ,(first literal-key)))))))
                             (format t "FRESH-ARTIFACT-PASS~%"))
                          :stream stream)))
               ;; Deliberately load neither ASDF nor Snowgrave in the child.
               (multiple-value-bind (output errors status)
                   (uiop:run-program
                    (test-process-command driver)
                    :output :string :error-output :output :ignore-error-status t)
                 (declare (ignore errors))
                 (check (and (zerop status) (search "FRESH-ARTIFACT-PASS" output))
                        "Fresh ~S replay failed (status ~D): ~A" mode status output))))
        (uiop:delete-directory-tree directory :validate t :if-does-not-exist :ignore)))))

(defun emitted-helper-p (source name)
  "Whether emitted source defines a function whose name begins with NAME."
  (flet ((prefixed-p (string)
           (and (<= (length name) (length string))
                (string= name string :end2 (length name)))))
    (loop for form in source
          thereis (and (consp form) (eq (first form) 'defun)
                       (let ((defined (second form)))
                         (and (symbolp defined) (prefixed-p (symbol-name defined))))))))

(defun pruned-helper-tests ()
  ;; A unit that never mentions a runtime query must not ship its machinery.
  (multiple-value-bind (unit package)
      (make-fixture
       :pruned-helpers
       "((defclass cell () ((value :initform 0 :accessor value)))
          (defun bump (object) (incf (value object))))"
       "(bump)" "((bump (cell)))" "(value (setf value))" :universe "(cell)")
    (declare (ignore package))
    (let ((source (snowgrave:unit-source unit)))
      (check (not (emitted-helper-p source "%LOGICAL-CLASS"))
             "Unused logical class table was emitted")
      (check (not (emitted-helper-p source "%LOGICAL-EQUALP"))
             "Unused logical EQUALP was emitted")
      (check (not (emitted-helper-p source "%METADATA-"))
             "Unused metadata queries were emitted")
      (check (emitted-helper-p source "%SLOT-READ")
             "An accessor's reader helper was pruned")))
  ;; Each query that is used must bring its machinery along.
  (multiple-value-bind (unit package)
      (make-fixture
       :retained-helpers
       "((defclass cell () ((value :initform 0)))
          (defun same (a b) (equalp a b))
          (defun kind (object) (class-name (class-of object))))"
       "(same kind)" "((same (cell cell)) (kind (cell)))" "()" :universe "(cell)")
    (declare (ignore package))
    (let ((source (snowgrave:unit-source unit)))
      (check (emitted-helper-p source "%LOGICAL-EQUALP")
             "A used EQUALP query lost its logical comparator")
      (check (emitted-helper-p source "%METADATA-CLASS-OF")
             "A used CLASS-OF query lost its logical descriptor")
      (check (emitted-helper-p source "%METADATA-CLASS-NAME")
             "A used CLASS-NAME query lost its logical descriptor"))))

(defun write-only-slot-test ()
  ;; A slot whose only source use is a constructor initarg still needs its
  ;; (setf reader); pruning must never emit a setf of an absent reader.
  (multiple-value-bind (unit package)
      (make-fixture
       :write-only-slot
       "((defclass cell () ((value :initarg :value)))
          (defun entry (n)
            (let ((object (make-instance 'cell :value n)))
              (declare (ignore object))
              :constructed)))"
       "(entry)" "((entry (number)))" "()" :universe "(cell)")
    (declare (ignore package))
    (compare-entry unit package "ENTRY" '(5) '((:constructed) nil))
    (let* ((definitions (loop for form in (snowgrave:unit-source unit)
                              when (and (consp form) (eq (first form) 'defun))
                                collect (second form)))
           (orphans (loop for name in definitions
                          when (and (consp name)
                                    (not (member (second name) definitions :test #'equal)))
                            collect name)))
      (check (null orphans) "Emitted setf writers without their reader functions: ~S" orphans))))

(defun string-literal-pool-test ()
  ;; A pool of only strings needs no recipe interpreter, but identity among
  ;; distinct equal strings and sharing of one string must still be preserved.
  (multiple-value-bind (unit package)
      (make-fixture
       :string-literal-pool
       "((defun entry ()
            (let ((a \"same\") (b \"same\") (c #1=\"shared\"))
              (values (equal a b) (eq a b)
                      (eq c #1#) (eq c \"shared\")))))"
       "(entry)" "((entry ()))" "()")
    (declare (ignore package))
    (compare-entry unit package "ENTRY" nil '((t nil t nil) nil))
    (let ((literal-form (find-if (lambda (form)
                                  (and (consp form) (eq (first form) 'defparameter)
                                       (search "%LITERALS" (symbol-name (second form)))))
                                (snowgrave:unit-source unit))))
      (check (and literal-form
                  (not (search "RECIPE" (princ-to-string literal-form)))
                  (search "COPY-SEQ" (princ-to-string literal-form)))
             "A strings-only literal pool did not take the direct path"))))

(defun undefined-reference-count (unit)
  "Number of undefined functions compiling UNIT's emitted source reports.
SBCL announces these as STYLE-WARNINGs, so a plain WARNING handler misses them."
  (let* ((path (merge-pathnames
                (format nil "snowgrave-undef-~D.lisp" (incf *fixture-sequence*))
                (uiop:temporary-directory)))
         (fasl (make-pathname :type "fasl" :defaults path))
         (count 0))
    (unwind-protect
         (let ((*error-output* (make-broadcast-stream))
               (*standard-output* (make-broadcast-stream)))
           (with-open-file (stream path :direction :output :if-exists :supersede)
             (snowgrave:write-unit-source unit stream))
           (handler-bind (((or style-warning warning)
                            (lambda (condition)
                              (when (search "undefined function" (princ-to-string condition))
                                (incf count)))))
             (compile-file path :output-file fasl))
           count)
      (ignore-errors (delete-file path))
      (ignore-errors (delete-file fasl)))))

(defun emitted-defun-names (unit)
  (loop for form in (snowgrave:unit-source unit)
        when (and (consp form) (eq (first form) 'defun))
          collect (second form)))

(defun self-contained-artifact-tests ()
  ;; A constructor writes its initform, so the unbound-slot slow path is
  ;; emitted. That slow path's store-value restart calls the runtime symbol
  ;; dispatchers, which must therefore be emitted too, even though no source
  ;; form ever reads a slot.
  (multiple-value-bind (unit package)
      (make-fixture
       :self-contained
       "((defclass cell () ((value :initform 1)))
          (defun entry () (let ((object (make-instance 'cell)))
                            (declare (ignore object))
                            :ok)))"
       "(entry)" "((entry ()))" "()" :universe "(cell)")
    (declare (ignore package))
    (check (zerop (undefined-reference-count unit))
           "Emitted source referenced an undefined function"))
  ;; The logical EQUALP comparator calls the logical metadata predicates, so a
  ;; unit whose only class use is EQUALP still needs the table, defined first.
  (multiple-value-bind (unit package)
      (make-fixture
       :ordering
       "((defclass cell () ((value :initform 1)))
          (defun make () (make-instance 'cell))
          (defun entry (object) (values (slot-value object 'value) (equalp object object))))"
       "(make entry)" "((make ()) (entry (cell)))" "()" :universe "(cell)")
    (check (zerop (undefined-reference-count unit))
           "A metadata-consuming artifact referenced an undefined function")
    ;; MAKE is typed as a function-returning entry; call the closed function directly.
    (let* ((symbol (find-symbol "MAKE" package))
           (made (funcall (snowgrave:unit-function unit symbol))))
      (check (equal '((1 t) nil)
                    (observed-call (snowgrave:unit-function unit (find-symbol "ENTRY" package))
                                   (list made)))
             "Logical EQUALP or literal slot read changed behaviour"))))
