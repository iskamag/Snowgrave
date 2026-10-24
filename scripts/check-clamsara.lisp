;;; Optional whole-source Clamsara integration gate, run in a fresh SBCL:
;;;   sbcl --dynamic-space-size 1024 --noinform --script scripts/check-clamsara.lisp \
;;;     /path/to/Clamsara/checkout /path/to/artifacts/
;;; Defaults: sibling Clamsara/.worktrees/sane-engine and .build/clamsara/.
;;; Closer MOP must be visible to ASDF; for a standalone checkout, set e.g.
;;; CL_SOURCE_REGISTRY=/path/to/closer-mop//: for this command.
;;; Exit zero requires native, closed, poisoned-original, fresh source, fresh
;;; compilation, and fresh FASL checks to pass. Any refusal or failure exits 1.
;;; Children load no Snowgrave, Clamsara, ASDF, or Closer MOP library.

(require :asdf)
(defparameter *snowgrave-root*
  (uiop:pathname-parent-directory-pathname
   (uiop:pathname-directory-pathname *load-truename*)))
(asdf:load-asd (merge-pathnames "snowgrave.asd" *snowgrave-root*))
(asdf:load-system "snowgrave")
(load (merge-pathnames "scripts/clamsara-source.lisp" *snowgrave-root*))

(defpackage #:snowgrave.clamsara-check (:use #:cl #:snowgrave.clamsara-source))
(in-package #:snowgrave.clamsara-check)

(defun git-output (checkout &rest arguments)
  (string-trim '(#\Newline #\Return)
               (uiop:run-program (append (list "git" "-C" (namestring checkout)) arguments)
                                 :output :string)))

(defun write-report (directory report)
  (with-open-file (stream (merge-pathnames "report.sexp" directory)
                          :direction :output :if-exists :supersede)
    (let ((*package* (find-package :cl)) (*print-pretty* t) (*print-readably* t))
      (write report :stream stream)
      (terpri stream))))

(defun source-fingerprints (paths root)
  (mapcar (lambda (path)
            (list (enough-namestring path root)
                  (subseq (uiop:run-program (list "sha256sum" (namestring path))
                                           :output :string)
                          0 64)))
          paths))

(defun phase-passed (report artifacts phase &rest details)
  (setf (getf report :phases)
        (append (getf report :phases) (list (list* :phase phase :status :passed details))))
  (write-report artifacts report))

(defun authored-function-names (forms)
  (let ((names nil))
    (dolist (form forms)
      (case (first form)
        ((defun defgeneric defmethod) (pushnew (second form) names :test #'equal))
        (defclass
         (dolist (slot (fourth form))
           (when (consp slot)
             (loop for (key value) on (rest slot) by #'cddr
                   do (case key
                        ((:reader :writer) (pushnew value names :test #'equal))
                        (:accessor (pushnew value names :test #'equal)
                                   (pushnew (list 'setf value) names :test #'equal)))))))))
    (nreverse names)))

(defun poison-original-functions (names)
  "Destroy original call paths only in this disposable integration process."
  (dolist (name names)
    (let* ((symbol (if (consp name) (second name) name))
           (original (fdefinition name))
           (poison (lambda (&rest arguments)
                     (declare (ignore arguments))
                     (error "Reached original Clamsara function ~S" name))))
      (when (eq (symbol-package symbol) (find-package :cl))
        (error "Refusing to poison a Common Lisp function: ~S" name))
      ;; Poison the generic object itself as well as its global binding, so a
      ;; retained reference to the original generic cannot escape this check.
      (when (typep original 'generic-function)
        (sb-mop:set-funcallable-instance-function original poison))
      (setf (fdefinition name) poison)))
  (length names))

(defun check-closed-workload (function expected phase)
  (let ((actual (funcall function)))
    (unless (eql actual expected)
      (error "~S returned ~S checks; native workload returned ~D" phase actual expected))
    (format t "~A: ~D original Clamsara checks passed.~%" phase actual)
    actual))

(defun function-name-key (name)
  (let ((symbol (if (consp name) (second name) name)))
    (list (package-name (symbol-package symbol)) (symbol-name symbol) (consp name))))

(defun run-child (artifacts phase source fasl key expected original-keys)
  (let* ((stem (string-downcase (symbol-name phase)))
         (driver (merge-pathnames (concatenate 'string stem ".lisp") artifacts))
         (log (merge-pathnames (concatenate 'string stem ".log") artifacts))
         (package (gensym "PACKAGE")) (compiled (gensym "COMPILED"))
         (warnings (gensym "WARNINGS")) (failure (gensym "FAILURE"))
         (original (gensym "ORIGINAL")) (symbol (gensym "SYMBOL")))
    (with-open-file (stream driver :direction :output :if-exists :supersede)
      (let ((*package* (find-package :cl)) (*print-readably* t)
            (*print-pretty* t) (*print-circle* t))
        (write
         `(progn
            (dolist (,package '("SNOWGRAVE" "CLAMSARA" "CLAMSARA.WORD-MEMORY"
                                "CLAMSARA.ENGINE-TESTS" "CLOSER-MOP" "ASDF"))
              (assert (not (find-package ,package))))
            ,(ecase phase
               (:fresh-source `(load ,(namestring source)))
               (:fresh-compile
                `(multiple-value-bind (,compiled ,warnings ,failure)
                     (compile-file ,(namestring source) :output-file ,(namestring fasl))
                   (declare (ignore ,warnings))
                   (assert (and ,compiled (not ,failure)))))
               (:fresh-fasl `(load ,(namestring fasl))))
            ,@(unless (eq phase :fresh-compile)
                `((dolist (,original ',original-keys)
                    (let* ((,package (find-package (first ,original)))
                           (,symbol (and ,package (find-symbol (second ,original) ,package))))
                      (assert (or (null ,symbol)
                                  (not (fboundp (if (third ,original)
                                                   (list 'setf ,symbol) ,symbol)))))))
                  (assert (= ,expected
                             (funcall (fdefinition (find-symbol ,(second key) ,(first key))))))))
            (format t "CLAMSARA-CHILD-PASS ~S~%" ,phase))
         :stream stream)
        (terpri stream)))
    (multiple-value-bind (output errors status)
        (uiop:run-program
         (list "timeout" "120" "sbcl" "--dynamic-space-size"
               (write-to-string (ceiling (sb-ext:dynamic-space-size) 1048576))
               "--noinform" "--no-sysinit" "--no-userinit"
               "--disable-debugger" "--script" (namestring driver))
         :output :string :error-output :output :ignore-error-status t)
      (declare (ignore errors))
      (with-open-file (stream log :direction :output :if-exists :supersede)
        (write-string output stream))
      (unless (and (zerop status) (search "CLAMSARA-CHILD-PASS" output))
        (error "~S failed with exit ~D; see ~A" phase status log))
      (format t "~A: passed in fresh SBCL; log ~A~%" phase log)
      (list :exit-status status :log (namestring log)))))

(defun test-symbol (name)
  (or (find-symbol name :clamsara.engine-tests)
      (error "Clamsara test symbol missing: ~A" name)))

(defun selected-workload (checkout)
  (let* ((functions (mapcar #'test-symbol
                           '("RUN-PROTECTED" "MAKE-FORMAT" "ALLOCATE-TWO"
                             "ADDRESS-OF" "CHENEY-CYCLES" "SWEEP-CYCLES"
                             "EVERY-REFERENCE-FLAVOR" "GRAPH-ORACLE")))
         (counter (test-symbol "*CHECKS*"))
         (forms (remove-if-not
                 (lambda (form)
                   (or (and (eq (first form) 'defun) (member (second form) functions))
                       (and (eq (first form) 'defvar) (eq (second form) counter))))
                 (read-definitions (merge-pathnames "test/engine.lisp" checkout)))))
    (dolist (name (cons counter functions))
      (unless (= 1 (count name forms :key #'second))
        (error "Expected exactly one workload definition for ~S" name)))
    ;; Preserve the selected source forms, including calls to the loaded CHECK
    ;; macro. Snowgrave owns their one-time macro normalization.
    (values forms counter
            (append
             (loop for name in '("CHENEY-CYCLES" "SWEEP-CYCLES" "EVERY-REFERENCE-FLAVOR")
                   append (loop for format in '(:pair :headered)
                                collect (list (test-symbol name) (list format))))
             (loop for family in '(:cheney :sweep)
                   append (loop for seed in '(1 7 42)
                                collect (list (test-symbol "GRAPH-ORACLE") (list seed family))))))))

(defun main (checkout artifacts)
  (let ((report (list :status :started :phases nil :checkout (namestring checkout)
                      :commit (git-output checkout "rev-parse" "HEAD")
                      :dirty (git-output checkout "status" "--porcelain")
                      :snowgrave-commit (git-output cl-user::*snowgrave-root* "rev-parse" "HEAD")
                      :snowgrave-dirty (git-output cl-user::*snowgrave-root* "status" "--porcelain")
                      :dynamic-space-mebibytes (ceiling (sb-ext:dynamic-space-size) 1048576)
                      :implementation (lisp-implementation-version)))
        (stage :load))
    (handler-case
        (progn
          ;; Explicit ASD registration takes precedence over another checkout
          ;; in the source registry. Verify the resulting systems before load.
          (asdf:load-asd (merge-pathnames "clamsara.asd" checkout))
          (dolist (name '("clamsara" "clamsara/word-memory" "clamsara/tests"))
            (unless (equal checkout (truename (asdf:system-source-directory name)))
              (error "ASDF resolved ~A outside the selected checkout" name)))
          (asdf:load-system "clamsara/tests")
          (setf (getf report :closer-mop-asd)
                (namestring (asdf:system-source-file "closer-mop"))
                (getf report :closer-mop-version)
                (asdf:component-version (asdf:find-system "closer-mop")))
          (setf (getf report :snowgrave-source-fingerprints)
                (source-fingerprints
                 (append (source-files (asdf:find-system "snowgrave"))
                         (list (merge-pathnames "snowgrave.asd" cl-user::*snowgrave-root*)
                               (merge-pathnames "scripts/check-clamsara.lisp" cl-user::*snowgrave-root*)))
                 cl-user::*snowgrave-root*))
          (phase-passed report artifacts :load)
          (setf stage :source)
          (let* ((paths (append (source-files (asdf:find-system "clamsara"))
                                (source-files (asdf:find-system "clamsara/word-memory"))))
                 (per-file (mapcar (lambda (path) (cons path (read-definitions path))) paths))
                 (engine-forms (mapcan (lambda (item) (copy-list (cdr item))) per-file)))
            (setf (getf report :source-files)
                  (mapcar (lambda (item)
                            (list (enough-namestring (car item) checkout) (length (cdr item))))
                          per-file)
                  (getf report :engine-model-definitions) (length engine-forms)
                  (getf report :external-operations) nil
                  (getf report :clamsara-source-fingerprints)
                  (source-fingerprints
                   (append paths (list (merge-pathnames "clamsara.asd" checkout)
                                       (merge-pathnames "test/engine.lisp" checkout)))
                   checkout))
            (format t "~&Clamsara ~A~%Checkout: ~A~%~D ASDF source files; ~D engine/model definitions.~%"
                    (getf report :commit) checkout (length paths) (length engine-forms))
            (dolist (item (getf report :source-files))
              (format t "  ~3D  ~A~%" (second item) (first item)))
            (multiple-value-bind (workload counter calls) (selected-workload checkout)
              (let* ((wrapper 'run-engine-workload)
                     (wrapper-form `(defun ,wrapper ()
                                      (let ((,counter 0))
                                        ,@(loop for (function arguments) in calls
                                                collect `(,function ,@(mapcar (lambda (value) `',value)
                                                                             arguments)))
                                        ,counter)))
                     (forms (append engine-forms workload (list wrapper-form)))
                     (native nil))
                (setf stage :native)
                (dolist (call calls)
                  (progv (list counter) (list 0)
                    (apply (first call) (second call))
                    (push (list :function (first call) :arguments (second call)
                                :checks (symbol-value counter)) native)
                    (format t "Native ~S ~S: ~D checks passed.~%"
                            (first call) (second call) (symbol-value counter))))
                (setf (getf report :native-checks) (nreverse native)
                      (getf report :native-check-total)
                      (reduce #'+ (getf report :native-checks) :key (lambda (row) (getf row :checks)))
                      (getf report :workload-definitions) (mapcar #'second workload)
                      (getf report :total-definitions) (length forms)
                      (getf report :entry) wrapper)
                (phase-passed report artifacts :native :checks (getf report :native-checks))
                (setf stage :close)
                (format t "Closing all ~D definitions; no external operations.~%"
                        (length forms))
                (finish-output)
                (let* ((unit
                         (snowgrave:close-source-unit
                          (list :forms forms) :unit-name :clamsara-whole-source
                          :universe (loop for form in engine-forms when (eq (first form) 'defclass)
                                            collect (second form))
                          :entries (list wrapper) :external-domains (list (list wrapper nil))
                          :external-operations nil))
                       (entry (snowgrave:unit-function unit wrapper))
                       (expected (getf report :native-check-total))
                       (metadata (snowgrave:unit-metadata unit))
                       (key (getf (find wrapper (getf metadata :entries)
                                       :key (lambda (row) (getf row :name))) :code-key))
                       (source (merge-pathnames "unit.lisp" artifacts))
                       (fasl (merge-pathnames "unit.fasl" artifacts)))
                  (phase-passed report artifacts :close)
                  (setf stage :closed-execution)
                  (check-closed-workload entry expected stage)
                  (phase-passed report artifacts stage :checks expected)
                  (setf stage :poisoned-execution)
                  (setf (getf report :poisoned-functions)
                        (authored-function-names (append engine-forms workload)))
                  (poison-original-functions (getf report :poisoned-functions))
                  (check-closed-workload entry expected stage)
                  (phase-passed report artifacts stage :checks expected
                                :poisoned-function-count (length (getf report :poisoned-functions)))
                  (setf stage :write-artifact)
                  (with-open-file (stream source :direction :output :if-exists :supersede)
                    (snowgrave:write-unit-source unit stream))
                  (with-open-file (stream (merge-pathnames "metadata.sexp" artifacts)
                                          :direction :output :if-exists :supersede)
                    (snowgrave:write-unit-metadata unit stream))
                  (setf (getf report :artifact-source-fingerprint)
                        (first (source-fingerprints (list source) artifacts)))
                  (phase-passed report artifacts stage)
                  (dolist (phase '(:fresh-source :fresh-compile :fresh-fasl))
                    (setf stage phase)
                    (let ((result (run-child artifacts phase source fasl key expected
                                             (mapcar #'function-name-key (getf report :poisoned-functions)))))
                      (apply #'phase-passed report artifacts phase result)))
                  (setf (getf report :status) :passed)
                  (write-report artifacts report)
                  (format t "Clamsara engine integration passed all phases (~D checks per execution).~%" expected)
                  0)))))
      (error (condition)
        (setf (getf report :status) (if (typep condition 'snowgrave:snowgrave-error) :refused :error)
              (getf report :stage) stage
              (getf report :condition) (princ-to-string (type-of condition))
              (getf report :detail) (princ-to-string condition))
        (when (typep condition 'snowgrave:snowgrave-error)
          (setf (getf report :feature) (snowgrave:error-feature condition)
                (getf report :detail) (snowgrave:error-detail condition)))
        (write-report artifacts report)
        (format t "~&Integration stopped at ~S: ~A~%No end-to-end pass; completed phases are recorded in report.sexp.~%"
                stage condition)
        1))))

(let* ((arguments (uiop:command-line-arguments))
       (checkout (truename (uiop:ensure-directory-pathname
                            (or (first arguments)
                                (merge-pathnames "../Clamsara/.worktrees/sane-engine/"
                                                 cl-user::*snowgrave-root*)))))
       (artifacts (uiop:ensure-directory-pathname
                   (or (second arguments) (merge-pathnames ".build/clamsara/" cl-user::*snowgrave-root*)))))
  (when (cddr arguments) (error "Usage: check-clamsara.lisp [checkout [artifacts]]"))
  (ensure-directories-exist (merge-pathnames "report.sexp" artifacts))
  (with-open-file (log (merge-pathnames "run.log" artifacts)
                       :direction :output :if-exists :supersede)
    (let* ((*standard-output* (make-broadcast-stream *standard-output* log))
           (*error-output* (make-broadcast-stream *error-output* log))
           (code (main checkout artifacts)))
      (finish-output *standard-output*)
      (finish-output *error-output*)
      (uiop:quit code))))
