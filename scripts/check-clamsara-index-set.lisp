;;;; Bounded component probe, not a collector end-to-end test.
;;;; Usage: sbcl --no-sysinit --no-userinit --script scripts/check-clamsara-index-set.lisp [Clamsara checkout]
(require :asdf)

(defparameter *probe-repository*
  (uiop:pathname-parent-directory-pathname
   (uiop:pathname-directory-pathname *load-truename*)))
(asdf:load-asd (merge-pathnames "snowgrave.asd" *probe-repository*))
(asdf:load-system "snowgrave")
(asdf:load-system "snowgrave/host-tools")

(load (merge-pathnames "scripts/clamsara-source.lisp" *probe-repository*))
(defparameter *probe-clamsara* (snowgrave.clamsara-source:clamsara-checkout))
(defparameter *probe-source* (merge-pathnames "engine/index-set.lisp" *probe-clamsara*))
(defparameter *probe-source-text* (uiop:read-file-string *probe-source*))
(unless (find-package "CLAMSARA") (make-package "CLAMSARA" :use '("COMMON-LISP")))

;; Read every definition of the original file without changing its source.
(defparameter *probe-forms*
  (let ((*package* (find-package "CLAMSARA")) (*read-eval* nil))
    (with-input-from-string (stream *probe-source-text*)
      (loop for form = (read stream nil stream) until (eq form stream)
            unless (eq (first form) 'in-package) collect form))))
(defparameter *probe-observation*
  (let ((*package* (find-package "CLAMSARA")) (*read-eval* nil))
    (read-from-string
     "(defun snowgrave-index-set-observation ()
        (let* ((set (make-index-set 4097))
               (sizes (loop for level = (slot-value set 'leaf)
                              then (slot-value level 'parent)
                            while level collect (length (slot-value level 'words))))
               (initial-empty (index-set-empty-p set)))
          (labels ((drain ()
                     (let ((result nil))
                       (loop
                         (multiple-value-bind (index present) (pop-first-index set)
                           (unless present (return (nreverse result)))
                           (push index result))))))
            (dolist (index '(4096 0 31 32 1023 1024 2048 4095 32 0))
              (write-index set index 1))
            (let* ((presence (mapcar (lambda (index) (index-present-p set index))
                                     '(0 32 4096 33)))
                   (ordered (drain))
                   (drained-empty (index-set-empty-p set))
                   (empty-pop (multiple-value-list (pop-first-index set))))
              (dolist (index '(17 1024 4096)) (write-index set index 1))
              (clear-index-set set)
              (let ((cleared-empty (index-set-empty-p set)))
                (dolist (index '(4096 32 0)) (write-index set index 1))
                (let ((reused (drain)))
                  (list sizes initial-empty presence ordered drained-empty empty-pop
                        cleared-empty reused (index-set-empty-p set))))))))")))
(defparameter *probe-expected*
  '((129 5 1) t (t t t nil) (0 31 32 1023 1024 2048 4095 4096)
    t (nil nil) t (0 32 4096) t))

(defun run-probe-child (path)
  (multiple-value-bind (output errors status)
      (uiop:run-program
       (append (list "timeout" "90s") (snowgrave.host-tools:host-process-command path))
       :output :string :error-output :output :ignore-error-status t)
    (declare (ignore errors))
    (unless (zerop status) (error "Fresh artifact probe exited ~D:~%~A" status output))
    (unless (search "INDEX-SET-ARTIFACT-PASS" output)
      (error "Fresh artifact probe did not report success:~%~A" output))))

(defun write-probe-driver (path forms)
  (with-open-file (stream path :direction :output :if-exists :supersede)
    (let ((*package* (find-package "COMMON-LISP")) (*print-readably* nil) (*print-escape* t) (*print-circle* t))
      (dolist (form forms) (write form :stream stream) (terpri stream)))))

(let* ((forms (append *probe-forms* (list *probe-observation*)))
       (entry (second *probe-observation*)))
  (assert (= 2 (count 'defclass *probe-forms* :key #'first)))
  (assert (= 7 (count 'defun *probe-forms* :key #'first)))
  (dolist (form forms) (eval form))
  (let* ((original (funcall (fdefinition entry)))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name :clamsara-complete-index-set
                :entries (list entry) :external-domains (list (list entry nil))))
         (closed (funcall (snowgrave:unit-function unit entry)))
         (key (getf (first (getf (snowgrave:unit-metadata unit) :entries)) :code-key))
         (directory (merge-pathnames
                     (format nil "snowgrave-clamsara-index-set-~D/" (get-universal-time))
                     (uiop:temporary-directory)))
         (source (merge-pathnames "unit.lisp" directory))
         (driver (merge-pathnames "run.lisp" directory)))
    (assert (equal original *probe-expected*))
    (assert (equal closed original))
    ;; Poison all original component functions before repeating the closed call.
    (dolist (form *probe-forms*)
      (when (eq (first form) 'defun)
        (setf (fdefinition (second form))
              (lambda (&rest arguments)
                (declare (ignore arguments)) (error "Original index-set function called")))))
    (assert (equal (funcall (snowgrave:unit-function unit entry)) original))
    (ensure-directories-exist source)
    (unwind-protect
         (progn
           (with-open-file (stream source :direction :output :if-exists :supersede)
             (snowgrave:write-unit-source unit stream))
           ;; Compilation and each replay use distinct fresh host processes.
           (dolist (mode '(:source :compile :fasl))
             (write-probe-driver
              driver
              `((assert (null (find-package "SNOWGRAVE")))
                (assert (null (find-package "CLAMSARA")))
                ,(if (eq mode :compile)
                     `(multiple-value-bind (path warnings failure)
                          (compile-file ,(namestring source))
                        (declare (ignore path warnings)) (assert (not failure)))
                     `(progn
                        (load ,(if (eq mode :source) (namestring source) `(compile-file-pathname ,(namestring source))))
                        (assert (equal ',original
                                       (funcall (fdefinition
                                                 (find-symbol ,(second key) ,(first key))))))))
                ;; Serialization may recreate a symbol-only package for names
                ;; used as lexical variables in generated helpers. No compiler
                ;; functions, variables, or classes may be installed there.
                (let ((package (find-package "SNOWGRAVE")))
                  (when package
                    (do-symbols (symbol package)
                      (when (eq (symbol-package symbol) package)
                        (assert (not (fboundp symbol)))
                        (assert (not (boundp symbol)))
                        (assert (null (find-class symbol nil)))))))
                (format t "INDEX-SET-ARTIFACT-PASS~%")))
             (run-probe-child driver))
           (assert (string= *probe-source-text* (uiop:read-file-string *probe-source*)))
           (format t "~&Complete Clamsara index-set component passed original/closed comparison,~%original-function poisoning, and separate fresh source/compile/FASL processes.~%Source: ~A~%Observation: ~S~%Not a collector end-to-end or native-target test.~%"
                   *probe-source* original))
      (uiop:delete-directory-tree directory :validate t :if-does-not-exist :ignore))))
