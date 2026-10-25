;;; Shared cold source inventory for the optional Clamsara gates.
(defpackage #:snowgrave.clamsara-source (:use #:cl)
  (:export #:source-files #:read-definitions #:clamsara-checkout #:register-clamsara-checkout))
(in-package #:snowgrave.clamsara-source)

(defun clamsara-checkout (&optional (argument (first (uiop:command-line-arguments))))
  (let* ((environment (uiop:getenv "SNOWGRAVE_CLAMSARA_ROOT"))
         (path (or (and environment (plusp (length environment)) environment)
                   argument
                   (error "Set SNOWGRAVE_CLAMSARA_ROOT to a Clamsara engine-rewrite checkout.")))
         (root (truename (uiop:ensure-directory-pathname path))))
    (unless (and (probe-file (merge-pathnames "clamsara.asd" root))
                 (probe-file (merge-pathnames "engine/index-set.lisp" root)))
      (error "Not a Clamsara engine-rewrite checkout: ~A" root))
    root))

(defun register-clamsara-checkout (root)
  ;; LOAD-ASD alone can be displaced by a different registered source file.
  ;; Give the explicit checkout precedence in this disposable gate process.
  (pushnew root asdf:*central-registry* :test #'equal)
  (asdf:load-asd (merge-pathnames "clamsara.asd" root)))

(defun source-files (component)
  (cond ((typep component 'asdf:cl-source-file)
         (list (truename (asdf:component-pathname component))))
        ((typep component 'asdf:parent-component)
         (mapcan #'source-files (asdf:component-children component)))))

(defun read-definitions (path)
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
