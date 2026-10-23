;;; Optional whole-source Clamsara integration gate, run in a fresh SBCL:
;;;   sbcl --noinform --script scripts/check-clamsara.lisp \
;;;     /path/to/Clamsara/checkout /path/to/artifacts/
;;; Defaults: sibling Clamsara/.worktrees/sane-engine and .build/clamsara/.
;;; Closer MOP must be visible to ASDF; for a standalone checkout, set e.g.
;;; CL_SOURCE_REGISTRY=/path/to/closer-mop//: for this command.
;;; This bounded gate runs the original Cheney workloads and attempts closure.
;;; A refusal exits 1. If closure becomes possible, exit 2 explicitly requests
;;; the remaining closed execution, poisoning, and fresh source/FASL checks.
;;; Neither outcome is an end-to-end integration success.

(require :asdf)
(defparameter *snowgrave-root*
  (uiop:pathname-parent-directory-pathname
   (uiop:pathname-directory-pathname *load-truename*)))
(asdf:load-asd (merge-pathnames "snowgrave.asd" *snowgrave-root*))
(asdf:load-system "snowgrave")

(defpackage #:snowgrave.clamsara-check (:use #:cl))
(in-package #:snowgrave.clamsara-check)

(defun source-files (component)
  "Keep the ASDF component order; do not substitute a hand-picked file list."
  (cond ((typep component 'asdf:cl-source-file)
         (list (truename (asdf:component-pathname component))))
        ((typep component 'asdf:parent-component)
         (mapcan #'source-files (asdf:component-children component)))))

(defun read-definitions (path)
  "Only package setup is consumed here. Every other top-level form is kept."
  (let ((*package* (find-package :cl-user)) (*read-eval* nil) (forms nil))
    (with-open-file (stream path)
      (loop for form = (read stream nil stream) until (eq form stream)
            do (case (and (consp form) (first form))
                 (defpackage (eval form))
                 (in-package
                  (setf *package* (or (find-package (second form))
                                      (error "Missing reader package ~S" (second form)))))
                 (otherwise (push form forms)))))
    (nreverse forms)))

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

(defun test-symbol (name)
  (or (find-symbol name :clamsara.engine-tests)
      (error "Clamsara test symbol missing: ~A" name)))

(defun selected-workload (checkout)
  (let* ((functions (mapcar #'test-symbol
                           '("RUN-PROTECTED" "MAKE-FORMAT" "ALLOCATE-TWO"
                             "ADDRESS-OF" "CHENEY-CYCLES")))
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
    (values forms counter (test-symbol "CHENEY-CYCLES"))))

(defun main (checkout artifacts)
  (let ((report (list :status :started :checkout (namestring checkout)
                      :commit (git-output checkout "rev-parse" "HEAD")
                      :dirty (git-output checkout "status" "--porcelain")
                      :snowgrave-commit (git-output cl-user::*snowgrave-root* "rev-parse" "HEAD")
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
          (setf stage :source)
          (let* ((paths (append (source-files (asdf:find-system "clamsara"))
                                (source-files (asdf:find-system "clamsara/word-memory"))))
                 (per-file (mapcar (lambda (path) (cons path (read-definitions path))) paths))
                 (engine-forms (mapcan (lambda (item) (copy-list (cdr item))) per-file))
                 (externals
                   (mapcar (lambda (name)
                             (or (find-symbol name :closer-mop)
                                 (error "Missing Closer MOP operation ~A" name)))
                           '("FINALIZE-INHERITANCE" "CLASS-SLOTS" "SLOT-DEFINITION-NAME"
                             "SLOT-DEFINITION-ALLOCATION" "SLOT-DEFINITION-TYPE"))))
            (setf (getf report :source-files)
                  (mapcar (lambda (item)
                            (list (enough-namestring (car item) checkout) (length (cdr item))))
                          per-file)
                  (getf report :engine-model-definitions) (length engine-forms)
                  (getf report :external-operations) externals)
            (format t "~&Clamsara ~A~%Checkout: ~A~%~D ASDF source files; ~D engine/model definitions.~%"
                    (getf report :commit) checkout (length paths) (length engine-forms))
            (dolist (item (getf report :source-files))
              (format t "  ~3D  ~A~%" (second item) (first item)))
            (multiple-value-bind (workload counter cycles) (selected-workload checkout)
              (let* ((wrapper 'run-cheney-workload)
                     (wrapper-form `(defun ,wrapper ()
                                      (let ((,counter 0))
                                        (,cycles :pair) (,cycles :headered) ,counter)))
                     (forms (append engine-forms workload (list wrapper-form)))
                     (native nil))
                (setf stage :native)
                (dolist (format '(:pair :headered))
                  (progv (list counter) (list 0)
                    (funcall cycles format)
                    (push (list format (symbol-value counter)) native)
                    (format t "Native CHENEY-CYCLES ~S: ~D checks passed.~%"
                            format (symbol-value counter))))
                (setf (getf report :native-checks) (nreverse native)
                      (getf report :workload-definitions) (mapcar #'second workload)
                      (getf report :total-definitions) (length forms)
                      (getf report :entry) wrapper)
                (write-report artifacts report)
                (setf stage :close)
                (format t "Closing all ~D definitions; five explicit external MOP operations.~%"
                        (length forms))
                (finish-output)
                (snowgrave:close-source-unit
                 (list :forms forms) :unit-name :clamsara-whole-source
                 :universe (loop for form in engine-forms when (eq (first form) 'defclass)
                                   collect (second form))
                 :entries (list wrapper) :external-domains (list (list wrapper nil))
                 :external-operations externals)
                (setf (getf report :status) :closure-produced-but-unvalidated
                      (getf report :closed-execution) :not-run
                      (getf report :fresh-source-fasl-replay) :not-run)
                (write-report artifacts report)
                (format t "Closure produced. Closed execution, poisoning and fresh replay remain unchecked.~%")
                2))))
      (error (condition)
        (setf (getf report :status) (if (typep condition 'snowgrave:snowgrave-error) :refused :error)
              (getf report :stage) stage
              (getf report :condition) (princ-to-string (type-of condition))
              (getf report :detail) (princ-to-string condition))
        (when (typep condition 'snowgrave:snowgrave-error)
          (setf (getf report :feature) (snowgrave:error-feature condition)
                (getf report :detail) (snowgrave:error-detail condition)))
        (write-report artifacts report)
        (format t "~&Integration stopped at ~S: ~A~%No closed workload or replay has passed.~%"
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
