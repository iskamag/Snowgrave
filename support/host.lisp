;;; Measurement and fresh-process adapters belong to tests, not the library.
(defpackage #:snowgrave.host-tools (:use #:cl)
  (:export #:host-gc #:host-bytes-consed #:host-process-command #:host-heap-mebibytes))
(in-package #:snowgrave.host-tools)

(defun host-gc ()
  #+sbcl (sb-ext:gc :full t)
  #+ccl (ccl:gc)
  #+ecl (ext:gc t))

(defun host-bytes-consed ()
  #+sbcl (sb-ext:get-bytes-consed)
  #+ccl (ccl::total-bytes-allocated)
  #-(or sbcl ccl) nil)

(defun host-process-command (driver)
  (let ((host (or (uiop:getenv "SNOWGRAVE_REPLAY_LISP")
                  #+sbcl "sbcl" #+ccl "ccl" #+ecl "ecl"
                  #-(or sbcl ccl ecl) (lisp-implementation-type))))
    (append (cond ((string-equal host "sbcl")
                   (list "sbcl" "--dynamic-space-size" (princ-to-string (or (host-heap-mebibytes) 1024))
                         "--noinform" "--no-sysinit" "--no-userinit" "--disable-debugger" "--script"))
                  ((string-equal host "ccl") '("ccl" "--no-init" "--batch" "--load"))
                  ((string-equal host "ecl") '("ecl" "-norc" "-shell"))
                  (t (error "No test process adapter for ~A." host)))
            (list (namestring driver)))))

(defun host-heap-mebibytes ()
  #+sbcl (ceiling (sb-ext:dynamic-space-size) 1048576)
  #-sbcl nil)
