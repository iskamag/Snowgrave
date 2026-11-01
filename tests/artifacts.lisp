(in-package #:snowgrave.tests)

(defun fresh-artifact-test ()
  (multiple-value-bind (unit package)
      (make-fixture
       :artifact
       "((defclass cell () ((value :initarg :value :reader value :type fixnum)
                            (scale :initform 0d0 :type double-float)
                            (next :initform nil :type (or null cell))))
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

(defun write-child-driver (stream form)
  "Write FORM as a child driver, printed from CL-USER.
The child has neither Snowgrave nor the test package, so any name interned in
either would read back unqualified-but-unresolvable. Printing from CL-USER
keeps the driver's own locals readable."
  (let ((*package* (find-package :cl-user))
        (*print-readably* nil)
        (*print-circle* t))
    (write form :stream stream)
    (terpri stream)))

(defun child-replay-succeeds-p (driver sentinel)
  "Whether DRIVER runs in a fresh child and writes SENTINEL.
A printed marker is not enough: a failing child echoes its own source in the
backtrace, so a search would find the literal marker text in the failure."
  (ignore-errors (delete-file sentinel))
  ;; Same adapter the suite uses elsewhere, so a replay runs under the host
  ;; that is actually executing the tests instead of always under SBCL.
  (uiop:run-program (test-process-command driver)
                    :output :string :error-output :output :ignore-error-status t)
  (probe-file sentinel))

(defun package-replay-test ()
  "A unit printed with single-colon qualifiers must still read back in a fresh
image where the original source package is gone: that is how the fresh-source
replay phase loads an artifact. An external client's own package is the case
that matters, since it is absent from the child yet its symbols appear
single-colon."
  (let* ((index (incf *fixture-sequence*))
         (source-name (format nil "SNOWGRAVE.REPLAY.~D" index))
         (source-package (make-package source-name :use '("COMMON-LISP")))
         (external (intern "EXTERNAL-KEY" source-package))
         (entry (intern "ENTRY" source-package))
         (unit (snowgrave:close-source-unit
                (list :forms (list `(defun ,entry () ',external)))
                :unit-name (list :replay source-name)
                :entries (list entry)
                :external-domains (list (list entry nil))))
         (closed (snowgrave::unit-plan-package (snowgrave::closed-unit-plan unit)))
         (closed-name (second (getf (find entry (getf (snowgrave:unit-metadata unit) :entries)
                                            :key (lambda (row) (getf row :name)))
                                    :code-key)))
         (path (merge-pathnames (format nil "snowgrave-replay-~D.lisp" index)
                                (uiop:temporary-directory)))
         (driver (merge-pathnames (format nil "snowgrave-replay-~D-run.lisp" index)
                                  (uiop:temporary-directory)))
         (sentinel (merge-pathnames (format nil "snowgrave-replay-~D-ok" index)
                                    (uiop:temporary-directory)))
         ;; The driver is read by a child, so its locals must be written as
         ;; interned names the child will also have, never gensym syntax.
         (resolved-name (intern "SNOWGRAVE-REPLAY-RESULT" :cl-user))
         (stream-name (intern "SNOWGRAVE-REPLAY-STREAM" :cl-user)))
    (export external source-package)
    (unwind-protect
         (progn
           (with-open-file (stream path :direction :output :if-exists :supersede)
             (snowgrave:write-unit-source unit stream))
           (with-open-file (stream driver :direction :output :if-exists :supersede)
             (write-child-driver
              stream
              `(progn
                 (when (find-package "SNOWGRAVE")
                   (error "Snowgrave leaked into the child"))
                 (when (find-package ,source-name)
                   (error "The source package still exists"))
                 (load ,(namestring path))
                 (let ((,resolved-name
                         (funcall (fdefinition (find-symbol ,closed-name ,closed)))))
                   (unless (and (eq (symbol-package ,resolved-name)
                                    (find-package ,source-name))
                                (string= (symbol-name ,resolved-name) ,(symbol-name external)))
                     (error "The quoted symbol resolved as ~S" ,resolved-name)))
                 (with-open-file (,stream-name ,(namestring sentinel)
                                               :direction :output
                                               :if-exists :supersede)
                   (write-line "ok" ,stream-name)))))
           (check (child-replay-succeeds-p driver sentinel)
                  "Fresh replay of a deleted source package failed"))
      (ignore-errors (delete-file path))
      (ignore-errors (delete-file driver))
      (ignore-errors (delete-file sentinel)))))

(defun multi-package-replay-test ()
  "A cohort quoting symbols from two different client packages must bootstrap
both, so the artifact reads back where neither package exists. One package is
not a strong enough test: each gets its own bootstrap form, and dropping or
collapsing one shows up only with more than one."
  (let* ((index (incf *fixture-sequence*))
         (names (list (format nil "SNOWGRAVE.CLIENT-A.~D" index)
                      (format nil "SNOWGRAVE.CLIENT-B.~D" index)))
         (packages (mapcar (lambda (name) (make-package name :use '("COMMON-LISP"))) names))
         (keys (mapcar (lambda (package) (intern "EXTERNAL-KEY" package)) packages))
         (entry (intern "ENTRY" (make-package (format nil "SNOWGRAVE.ENTRY.~D" index)
                                              :use '("COMMON-LISP"))))
         (unit (snowgrave:close-source-unit
                (list :forms (list `(defun ,entry () (values ,@(mapcar (lambda (key) `',key) keys)))))
                :unit-name (list :multi index) :entries (list entry)
                :external-domains (list (list entry nil))))
         (closed (snowgrave::unit-plan-package (snowgrave::closed-unit-plan unit)))
         (closed-name (second (getf (find entry (getf (snowgrave:unit-metadata unit) :entries)
                                            :key (lambda (row) (getf row :name)))
                                    :code-key)))
         (path (merge-pathnames (format nil "snowgrave-multi-~D.lisp" index)
                                (uiop:temporary-directory)))
         (driver (merge-pathnames (format nil "snowgrave-multi-~D-run.lisp" index)
                                  (uiop:temporary-directory)))
         (sentinel (merge-pathnames (format nil "snowgrave-multi-~D-ok" index)
                                    (uiop:temporary-directory)))
         (resolved-name (intern "SNOWGRAVE-REPLAY-RESULT" :cl-user))
         (symbol-name (intern "SNOWGRAVE-REPLAY-SYMBOL" :cl-user))
         (stream-name (intern "SNOWGRAVE-REPLAY-STREAM" :cl-user)))
    (dolist (package packages) (export (intern "EXTERNAL-KEY" package) package))
    (unwind-protect
         (progn
           (with-open-file (stream path :direction :output :if-exists :supersede)
             (snowgrave:write-unit-source unit stream))
           (with-open-file (stream driver :direction :output :if-exists :supersede)
             (write-child-driver
              stream
              `(progn
                 (when (find-package "SNOWGRAVE")
                   (error "Snowgrave leaked into the child"))
                 ,@(loop for name in names
                         collect `(when (find-package ,name)
                                    (error "~A still exists" ,name)))
                 (load ,(namestring path))
                 (let ((,resolved-name
                         (mapcar (lambda (,symbol-name)
                                   (package-name (symbol-package ,symbol-name)))
                                 (multiple-value-list
                                  (funcall (fdefinition (find-symbol ,closed-name ,closed)))))))
                   (unless (equal ,resolved-name (list ,@names))
                     (error "Quoted client symbols resolved as ~S" ,resolved-name)))
                 (with-open-file (,stream-name ,(namestring sentinel)
                                               :direction :output
                                               :if-exists :supersede)
                   (write-line "ok" ,stream-name)))))
           (check (child-replay-succeeds-p driver sentinel)
                  "Replay of two deleted client packages failed"))
      (ignore-errors (delete-file path))
      (ignore-errors (delete-file driver))
      (ignore-errors (delete-file sentinel)))))

(defun shared-export-replay-test ()
  "Two client packages exporting the same name must bootstrap it in both, and
the child must still get two distinct symbols. A bootstrap keyed by name alone
would collapse them into one."
  (let* ((index (incf *fixture-sequence*))
         (names (list (format nil "SNOWGRAVE.SHARED-A.~D" index)
                      (format nil "SNOWGRAVE.SHARED-B.~D" index)))
         (packages (mapcar (lambda (name) (make-package name :use '("COMMON-LISP"))) names))
         (keys (mapcar (lambda (package) (intern "SHARED-NAME" package)) packages))
         (entry (intern "ENTRY" (make-package (format nil "SNOWGRAVE.SENTRY.~D" index)
                                              :use '("COMMON-LISP"))))
         (unit (snowgrave:close-source-unit
                (list :forms (list `(defun ,entry () (values ,@(mapcar (lambda (key) `',key) keys)))))
                :unit-name (list :shared index) :entries (list entry)
                :external-domains (list (list entry nil))))
         (closed (snowgrave::unit-plan-package (snowgrave::closed-unit-plan unit)))
         (closed-name (second (getf (find entry (getf (snowgrave:unit-metadata unit) :entries)
                                            :key (lambda (row) (getf row :name)))
                                    :code-key)))
         (path (merge-pathnames (format nil "snowgrave-shared-~D.lisp" index)
                                (uiop:temporary-directory)))
         (driver (merge-pathnames (format nil "snowgrave-shared-~D-run.lisp" index)
                                  (uiop:temporary-directory)))
         (sentinel (merge-pathnames (format nil "snowgrave-shared-~D-ok" index)
                                    (uiop:temporary-directory)))
         (resolved-name (intern "SNOWGRAVE-REPLAY-RESULT" :cl-user))
         (stream-name (intern "SNOWGRAVE-REPLAY-STREAM" :cl-user)))
    (dolist (package packages) (export (intern "SHARED-NAME" package) package))
    (unwind-protect
         (progn
           (with-open-file (stream path :direction :output :if-exists :supersede)
             (snowgrave:write-unit-source unit stream))
           (with-open-file (stream driver :direction :output :if-exists :supersede)
             (write-child-driver
              stream
              `(progn
                 ,@(loop for name in names
                         collect `(when (find-package ,name)
                                    (error "~A still exists" ,name)))
                 (load ,(namestring path))
                 (let ((,resolved-name
                         (multiple-value-list
                          (funcall (fdefinition (find-symbol ,closed-name ,closed))))))
                   (unless (and (= 2 (length ,resolved-name))
                                (not (eq (first ,resolved-name) (second ,resolved-name)))
                                (equal (mapcar (lambda (symbol)
                                                 (package-name (symbol-package symbol)))
                                               ,resolved-name)
                                       (list ,@names)))
                     (error "Shared exports did not stay distinct: ~S" ,resolved-name)))
                 (with-open-file (,stream-name ,(namestring sentinel)
                                               :direction :output
                                               :if-exists :supersede)
                   (write-line "ok" ,stream-name)))))
           (check (child-replay-succeeds-p driver sentinel)
                  "Replay of two packages sharing an exported name failed"))
      (ignore-errors (delete-file path))
      (ignore-errors (delete-file driver))
      (ignore-errors (delete-file sentinel)))))

(defun reexport-replay-test ()
  "A symbol re-exported by a second package is one identity. The artifact names
its home package, and the child gets the original symbol back from both uses."
  (let* ((index (incf *fixture-sequence*))
         (home (format nil "SNOWGRAVE.HOME.~D" index))
         (relay (format nil "SNOWGRAVE.RELAY.~D" index))
         (home-package (make-package home :use '("COMMON-LISP")))
         (relay-package (make-package relay :use '("COMMON-LISP")))
         (payload (intern "PAYLOAD" home-package))
         (entry (intern "ENTRY" (make-package (format nil "SNOWGRAVE.RENTRY.~D" index)
                                              :use '("COMMON-LISP")))))
    (import payload relay-package)
    (export payload home-package)
    (export payload relay-package)
    (let* ((unit (snowgrave:close-source-unit
                  (list :forms (list `(defun ,entry ()
                                        (values ',payload
                                                ',(intern "PAYLOAD" relay-package)))))
                  :unit-name (list :reexport index) :entries (list entry)
                  :external-domains (list (list entry nil))))
           (closed (snowgrave::unit-plan-package (snowgrave::closed-unit-plan unit)))
           (closed-name (second (getf (find entry (getf (snowgrave:unit-metadata unit) :entries)
                                              :key (lambda (row) (getf row :name)))
                                      :code-key)))
           (path (merge-pathnames (format nil "snowgrave-reexport-~D.lisp" index)
                                  (uiop:temporary-directory)))
           (driver (merge-pathnames (format nil "snowgrave-reexport-~D-run.lisp" index)
                                    (uiop:temporary-directory)))
           (sentinel (merge-pathnames (format nil "snowgrave-reexport-~D-ok" index)
                                      (uiop:temporary-directory)))
           (resolved-name (intern "SNOWGRAVE-REPLAY-RESULT" :cl-user))
           (stream-name (intern "SNOWGRAVE-REPLAY-STREAM" :cl-user)))
      (unwind-protect
           (progn
             (with-open-file (stream path :direction :output :if-exists :supersede)
               (snowgrave:write-unit-source unit stream))
             (with-open-file (stream driver :direction :output :if-exists :supersede)
               (write-child-driver
                stream
                `(progn
                   (when (find-package ,relay)
                     (error "The relaying package still exists"))
                   (load ,(namestring path))
                   (let ((,resolved-name
                           (multiple-value-list
                            (funcall (fdefinition (find-symbol ,closed-name ,closed))))))
                     (unless (and (= 2 (length ,resolved-name))
                                  (eq (first ,resolved-name) (second ,resolved-name))
                                  (eq (symbol-package (first ,resolved-name))
                                      (find-package ,home)))
                       (error "A re-exported symbol lost its identity: ~S" ,resolved-name)))
                   (with-open-file (,stream-name ,(namestring sentinel)
                                                 :direction :output
                                                 :if-exists :supersede)
                     (write-line "ok" ,stream-name)))))
             (check (child-replay-succeeds-p driver sentinel)
                    "Replay of a re-exported symbol failed"))
        (ignore-errors (delete-file path))
        (ignore-errors (delete-file driver))
        (ignore-errors (delete-file sentinel))))))
