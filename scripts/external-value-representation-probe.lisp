(require :asdf)
(let* ((root (or (uiop:getenv "SNOWGRAVE_PROBE_SOURCE")
                 (uiop:pathname-parent-directory-pathname
                  (uiop:pathname-directory-pathname *load-truename*))))
       (cache (or (uiop:getenv "SNOWGRAVE_PROBE_CACHE")
                  "/tmp/snowgrave-external-value-probe-cache/")))
  (asdf:initialize-source-registry `(:source-registry (:directory ,root) :ignore-inherited-configuration))
  (asdf:initialize-output-translations `(:output-translations (t ,cache) :ignore-inherited-configuration)))
(asdf:load-system "snowgrave/sbcl")
(defpackage #:snowgrave.external-value.probe
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass #:defgeneric #:defmethod))
(in-package #:snowgrave.external-value.probe)
(defvar *captured* :initial)
(defun record-observer (x) (typep x 'standard-object))
(defun callable-observer (x) (typep x 'generic-function))
(defun state-observer () (typep *captured* 'generic-function))
(defun aggregate-observer () (typep (car *captured*) 'standard-object))
(defun function-observer () #'value)
(let ((baseline-p (member "baseline" (uiop:command-line-arguments) :test #'string=)))
  (loop for (label forms classes generics universe external feature) in
        '((:record ((defclass sample () ())
                    (defun entry () (record-observer (make-instance 'sample))))
                   (sample) () (sample) record-observer :external-value-representation)
          (:callable ((defgeneric value (x)) (defmethod value ((x number)) x)
                      (defun entry () (callable-observer #'value)))
                     () (value) (number) callable-observer :external-value-representation)
          (:shared-special ((defgeneric value (x)) (defmethod value ((x number)) x)
                            (defparameter *captured* #'value)
                            (defun entry () (state-observer)))
                           () (value) (number) state-observer :external-shared-state-representation)
          (:returned-identity ((defgeneric value (x)) (defmethod value ((x number)) x)
                               (defun entry () (eq #'value (function-observer))))
                              () (value) (number) function-observer :external-logical-identity)
          (:aggregate ((defclass sample () ()) (defparameter *captured* (list nil))
                       (defun entry () (setf (car *captured*) (make-instance 'sample))
                                      (aggregate-observer)))
                      (sample) () (sample) aggregate-observer :external-shared-state-representation))
        do (mapc #'eval forms)
           (let* ((ordinary (entry)) (before *captured*)
                  (identity (list 'external-value-probe label))
                  (result (handler-case
                              (snowgrave:close-source-unit
                               (list :forms forms) :unit-name identity
                               :closed-classes classes :closed-generics generics :universe universe
                               :entries '(entry) :external-domains '((entry ()))
                               :external-operations (list external))
                            (snowgrave:unclosed-call (condition) condition))))
             (assert ordinary)
             (if baseline-p
                 (let ((closed (funcall (snowgrave:unit-function result 'entry))))
                   (assert (not (eql ordinary closed)))
                   (format t "~S ORDINARY=~S CLOSED=~S CLAIM=~S~%"
                           label ordinary closed (getf (snowgrave:unit-report result) :claim)))
                 (progn
                   (assert (typep result 'snowgrave:unclosed-call))
                   (assert (eq (snowgrave:error-feature result) feature))
                   (assert (eq before *captured*))
                   (assert (not (find-package
                                 (format nil "SNOWGRAVE.UNIT.~A"
                                         (with-standard-io-syntax (write-to-string identity))))))
                   (format t "~S REJECTED=~S SHARED-STATE-PRESERVED~%" label feature)))))
  (format t "External representation probe completed (~A).~%" (if baseline-p "baseline" "repaired")))
