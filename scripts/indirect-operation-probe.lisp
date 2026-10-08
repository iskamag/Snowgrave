(require :asdf)
(let ((root (or (uiop:getenv "SNOWGRAVE_PROBE_SOURCE")
                (uiop:pathname-parent-directory-pathname
                 (uiop:pathname-directory-pathname *load-truename*)))))
  (asdf:initialize-source-registry `(:source-registry (:directory ,root) :ignore-inherited-configuration))
  (asdf:initialize-output-translations
   `(:output-translations (t ,(or (uiop:getenv "SNOWGRAVE_PROBE_CACHE")
                                 "/tmp/snowgrave-indirect-operation-probe-cache/")) :ignore-inherited-configuration)))
(asdf:load-system "snowgrave/sbcl")
(defpackage #:snowgrave.indirect-operation.probe
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass))
(in-package #:snowgrave.indirect-operation.probe)
(defun observe (x y) (declare (ignore x)) (typep y 'standard-object))
(let ((baseline-p (member "baseline" (uiop:command-line-arguments) :test #'string=)))
  (loop for expression in
        '((funcall #'format nil control (make-instance 'sample))
          (apply #'format (list nil control (make-instance 'sample)))
          (multiple-value-call #'format (values nil control)
                               (values (make-instance 'sample)))
          (funcall #'mapcar #'equalp (list (make-instance 'sample))
                                    (list (make-instance 'sample)))
          (apply #'mapcar (list #'equalp (list (make-instance 'sample))
                                       (list (make-instance 'sample))))
          (multiple-value-call #'mapcar
            (values #'equalp (list (make-instance 'sample)))
            (values (list (make-instance 'sample))))
          (let ((tail (identity (list (list (make-instance 'sample))))))
            (apply #'mapcar #'observe (list 17) tail)))
        for index from 0
        for feature = (cond ((< index 3) :printed-record-or-metaobject)
                            ((< index 6) :equalp-callback)
                            (t :external-callback-representation))
        when (or (not (member "tail-only" (uiop:command-line-arguments) :test #'string=))
                 (= index 6))
        do (let ((forms `((defclass sample () ()) (defun entry (control) ,expression))))
             (mapc #'eval forms)
             (let ((ordinary (entry "~S")))
               (if baseline-p
                   (let* ((unit (snowgrave:close-source-unit
                                 (list :forms forms) :unit-name (list 'indirect-operation-probe index)
                                 :closed-classes '(sample) :universe '(sample string)
                                 :entries '(entry) :external-domains '((entry (string)))
                                 :external-operations (when (= index 6) '(observe))))
                          (closed (funcall (snowgrave:unit-function unit 'entry) "~S")))
                     (assert (not (equal ordinary closed)))
                     (format t "~S ORDINARY=~S CLOSED=~S CLAIM=~S~%"
                             (car expression) (if (stringp ordinary) (subseq ordinary 0 2) ordinary)
                             (if (stringp closed) (subseq closed 0 2) closed)
                             (getf (snowgrave:unit-report unit) :claim)))
                   (if (<= 3 index 5)
                       (let* ((unit (snowgrave:close-source-unit
                                     (list :forms forms) :unit-name (list 'indirect-operation-probe index)
                                     :closed-classes '(sample) :universe '(sample string)
                                     :entries '(entry) :external-domains '((entry (string)))))
                              (closed (funcall (snowgrave:unit-function unit 'entry) "~S")))
                         (assert (equal ordinary closed))
                         (format t "~S ORDINARY=~S CLOSED=~S~%" (car expression) ordinary closed))
                   (let ((condition
                           (handler-case
                               (snowgrave:close-source-unit
                                (list :forms forms) :unit-name (list 'indirect-operation-probe index)
                                :closed-classes '(sample) :universe '(sample string)
                                :entries '(entry) :external-domains '((entry (string)))
                                :external-operations (when (= index 6) '(observe)))
                             (snowgrave:snowgrave-error (condition) condition))))
                     (assert (typep condition (if (< index 6) 'snowgrave:unclosed-class-operation
                                                 'snowgrave:unclosed-call)))
                     (assert (eq feature (snowgrave:error-feature condition)))
                     (format t "~S ORDINARY=~S REJECTED=~S~%" (car expression) ordinary feature)))))))
  (format t "Indirect operation public probe completed (~A).~%" (if baseline-p "baseline" "repaired")))
