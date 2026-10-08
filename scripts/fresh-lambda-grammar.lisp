(require :asdf)
(let* ((root (uiop:pathname-parent-directory-pathname
              (uiop:pathname-directory-pathname *load-truename*)))
       (cache (merge-pathnames ".build/fresh-lambda-grammar-fasl/" root)))
  (asdf:initialize-source-registry `(:source-registry (:directory ,root) :ignore-inherited-configuration))
  (asdf:initialize-output-translations `(:output-translations (t ,cache) :ignore-inherited-configuration)))
(asdf:load-system "snowgrave/sbcl")
(defpackage #:snowgrave.lambda-grammar.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defgeneric #:defmethod))
(in-package #:snowgrave.lambda-grammar.fixture)

;; The native source compiler rejects the same source which closure used to
;; normalize into a different, valid function before claiming semantic closure.
(let ((*error-output* (make-string-output-stream)))
  (multiple-value-bind (function warnings failure) (compile nil '(lambda ((x number)) x))
    (declare (ignore function warnings))
    (assert failure)))
(labels ((close-it (forms identity &optional generics)
           (snowgrave:close-source-unit
            (list :forms forms) :unit-name identity :universe '(number t)
            :closed-generics generics :entries '(entry) :external-domains '((entry (number))))))
  (loop for forms in '(((defun entry ((x number)) x))
                       ((defun entry (x) (funcall (lambda ((y number)) y) x)))
                       ((defun entry (x) (flet ((local ((y number)) y)) (local x))))
                       ((defun entry (x) (labels ((local ((y number)) y)) (local x))))
                       ((defun entry (x &rest (r nil)) (declare (ignore r)) x)))
        for index from 1 do
    (let ((condition (handler-case (close-it forms (list 'malformed-ordinary index))
                       (snowgrave:unsupported-definition (condition) condition))))
      (assert (typep condition 'snowgrave:unsupported-definition))
      (assert (member (snowgrave:error-feature condition) '(:lambda-list-required :lambda-list-rest)))))
  (assert (not (fboundp 'entry)))
  ;; Both open method installation and closed ordinary-body materialization
  ;; must retain valid specialization, optional defaults and supplied-p values.
  (let* ((forms '((defgeneric specialized (x &optional y))
                  (defmethod specialized ((x t) &optional (y :fallback yp)) (list :general x y yp))
                  (defmethod specialized ((x number) &optional (y (+ x 1) yp)) (list :number x y yp))
                  (defun entry (x) (list (specialized x) (specialized x 29)))))
         (unit (close-it forms '(valid-authored-specialized) '(specialized))))
    (dolist (form forms) (eval form))
    (assert (equal (funcall (snowgrave:unit-function unit 'entry) 17) (entry 17)))
    (assert (equal (entry 17) '((:number 17 18 nil) (:number 17 29 t))))))
(format t "Fresh ordinary and method lambda grammars executed.~%")
