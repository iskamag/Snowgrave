(require :asdf)
(let ((root (or (uiop:getenv "SNOWGRAVE_PROBE_SOURCE")
                (uiop:pathname-parent-directory-pathname
                 (uiop:pathname-directory-pathname *load-truename*)))))
  (asdf:initialize-source-registry `(:source-registry (:directory ,root) :ignore-inherited-configuration))
  (asdf:initialize-output-translations
   `(:output-translations (t ,(or (uiop:getenv "SNOWGRAVE_PROBE_CACHE")
                                 "/tmp/snowgrave-indirect-equalp-probe-cache/")) :ignore-inherited-configuration)))
(asdf:load-system "snowgrave/sbcl")
(defpackage #:snowgrave.indirect-equalp.probe
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass))
(in-package #:snowgrave.indirect-equalp.probe)
(let ((baseline-p (member "baseline" (uiop:command-line-arguments) :test #'string=)))
  (loop for call in '((funcall #'equalp (make-instance 'sample) (make-instance 'sample))
                     (apply #'equalp (list (make-instance 'sample) (make-instance 'sample)))
                     (multiple-value-call #'equalp (values (make-instance 'sample)) (values (make-instance 'sample))))
        for index from 0 do
          (let ((forms `((defclass sample () ((x :initform 17))) (defun entry () ,call))))
            (mapc #'eval forms)
            (let* ((ordinary (entry))
                   (unit (snowgrave:close-source-unit
                          (list :forms forms) :unit-name (list 'indirect-equalp-probe index)
                          :closed-classes '(sample) :universe '(sample)
                          :entries '(entry) :external-domains '((entry ()))))
                   (closed (funcall (snowgrave:unit-function unit 'entry))))
              (assert (null ordinary))
              (if baseline-p (assert closed) (assert (null closed)))
              (format t "~S ORDINARY=~S CLOSED=~S CLAIM=~S~%"
                      (car call) ordinary closed (getf (snowgrave:unit-report unit) :claim)))))
  (format t "Indirect EQUALP public probe completed (~A).~%" (if baseline-p "baseline" "repaired")))
