;;; Run from a checkout: sbcl --no-userinit --script scripts/bench-generic-call-conventions.lisp
;;; Inputs are allocated before measurement; only the entry's loop is measured.
(require :asdf)
(let ((root (uiop:pathname-parent-directory-pathname (uiop:pathname-directory-pathname *load-truename*))))
  (asdf:initialize-source-registry `(:source-registry (:directory ,root) :ignore-inherited-configuration))
  (asdf:initialize-output-translations
   `(:output-translations (t ,(merge-pathnames ".build/benchmark-fasl/" root)) :ignore-inherited-configuration))
  (asdf:load-system :snowgrave/sbcl))
(defpackage #:snowgrave.bench.generic-conventions (:use #:cl))
(in-package #:snowgrave.bench.generic-conventions)
(defvar *sink*)
(defun sample (tag label function)
  (dotimes (index 100) (funcall function 1000))
  (sb-ext:gc :full t)
  (let* ((before (sb-ext:get-bytes-consed)) (start (get-internal-run-time))
         (result (funcall function 100000))
         (bytes (- (sb-ext:get-bytes-consed) before))
         (seconds (/ (- (get-internal-run-time) start) (float internal-time-units-per-second))))
    (format t "~&GENERIC-COST ~S ~S result=~S calls=100000 bytes=~D seconds=~,6F~%"
            tag label result bytes seconds)
    (assert (= result 17))
    ;; Leave room for bounded host measurement noise; even one cons per call
    ;; exceeds this bound by more than an order of magnitude.
    (when (eq label :closed) (assert (< bytes 65536)))
    (when (eq tag :calibration) (assert (> bytes 1000000)))))
(defun run-case (tag optional indirect omitted &optional qualified)
  (let* ((*package* (make-package (format nil "SNOWGRAVE.BENCH.GENERIC.~A" tag) :use '("CL")))
         (lambda-list (if optional "&optional (owner 23)" "owner"))
         (forms (read-from-string
                 (format nil "((defgeneric operation (object bytes ~A))
                               ~A
                               (defmethod operation ((object t) (bytes t) ~A)
                                 (declare (ignore object bytes owner)) 17)
                               (defun relay (callback) (funcall callback 0 16 ~A))
                               (defun entry (count)
                                 (declare (type fixnum count))
                                 (let ((result 0)) (dotimes (index count result)
                                   (setf result ~A)))))"
                         (if optional "&optional owner" "owner")
                         (if qualified
                             (format nil "(defmethod operation :around ((object t) (bytes t) ~A)
                                           (declare (ignore object bytes owner)) (call-next-method))" lambda-list) "")
                         lambda-list
                         (if omitted "" "nil")
                         (if indirect "(relay #'operation)"
                             (if omitted "(operation 0 16)" "(operation 0 16 nil)")))))
         (entry (intern "ENTRY")))
    (dolist (form forms) (eval form))
    (let ((unit (snowgrave:close-source-unit
                 (list :forms forms) :unit-name (list :generic-call-bench tag)
                 :closed-generics (list (intern "OPERATION")) :universe '(fixnum t)
                 :entries (list entry) :external-domains (list (list entry '(fixnum))))))
      (sample tag :native (fdefinition entry))
      (sample tag :closed (snowgrave:unit-function unit entry)))))
(run-case :required nil nil nil)
(run-case :optional t nil nil)
(run-case :required-indirect nil t nil)
(run-case :optional-indirect t t nil)
(run-case :omitted t nil t)
(run-case :omitted-indirect t t t)
(run-case :optional-around t nil nil t)
(run-case :omitted-around-indirect t t t t)
(sample :calibration :allocating (lambda (count) (dotimes (index count 17) (setf *sink* (cons index nil)))))
