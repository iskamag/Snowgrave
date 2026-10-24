;;; Shared cold source inventory for the optional Clamsara gates.
(defpackage #:snowgrave.clamsara-source (:use #:cl)
  (:export #:source-files #:read-definitions))
(in-package #:snowgrave.clamsara-source)

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
