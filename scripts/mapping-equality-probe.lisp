(require :asdf)
(let ((root (or (uiop:getenv "SNOWGRAVE_PROBE_SOURCE")
                (uiop:pathname-parent-directory-pathname (uiop:pathname-directory-pathname *load-truename*)))))
  (asdf:initialize-source-registry `(:source-registry (:directory ,root) :ignore-inherited-configuration))
  (asdf:initialize-output-translations
   `(:output-translations (t ,(or (uiop:getenv "SNOWGRAVE_PROBE_CACHE")
                                 "/tmp/snowgrave-mapping-equality-probe-cache/")) :ignore-inherited-configuration)))
(asdf:load-system "snowgrave/sbcl")
(defpackage #:snowgrave.mapping-equality.probe
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass))
(in-package #:snowgrave.mapping-equality.probe)
(let ((baseline-p (member "baseline" (uiop:command-line-arguments) :test #'string=)))
  (loop for expression in
        '((mapcar #'equalp (list p p) (list p q))
          (funcall #'mapcar #'equalp (list p p) (list p q))
          (apply #'mapcar (list #'equalp (list p p) (list p q)))
          (multiple-value-call #'mapcar (values) (values #'equalp (list p p)) (values (list p q)))
          (eq p (car (mapc #'equalp (list p p) (list p q)))))
        for index from 0 do
    (let* ((forms `((defclass sample () ())
                   (defun entry ()
                     (let ((p (make-instance 'sample)) (q (make-instance 'sample))) ,expression))))
           (unit (handler-case
                     (snowgrave:close-source-unit
                      (list :forms forms) :unit-name (list 'mapping-equality-probe index)
                      :closed-classes '(sample) :universe '(sample)
                      :entries '(entry) :external-domains '((entry ())))
                   (snowgrave:snowgrave-error (condition) condition))))
      (mapc #'eval forms)
      (let ((ordinary (entry)))
        (if baseline-p
            (progn
              (assert (typep unit 'snowgrave:unclosed-class-operation))
              (assert (eq :equalp-callback (snowgrave:error-feature unit)))
              (format t "~S ORDINARY=~S REJECTED=~S~%" (car expression) ordinary (snowgrave:error-feature unit)))
            (let ((closed (funcall (snowgrave:unit-function unit 'entry))))
              (assert (equal ordinary closed))
              (format t "~S ORDINARY=~S CLOSED=~S~%" (car expression) ordinary closed))))))
  (format t "Mapping equality public probe completed (~A).~%" (if baseline-p "baseline" "supported")))
