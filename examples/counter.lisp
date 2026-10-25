;;; Load from the repository root after registering the ASDF dependencies.
(require :asdf)
(let ((root (uiop:pathname-parent-directory-pathname
             (uiop:pathname-directory-pathname *load-truename*))))
  (asdf:load-asd (merge-pathnames "snowgrave.asd" root))
  (asdf:load-system "snowgrave"))

(defpackage #:snowgrave.example.counter (:use #:cl))
(in-package #:snowgrave.example.counter)

;; These forms are the owned program. Snowgrave creates its disposable CLOS
;; definitions and closed structures; no original definitions need installing.
(defparameter *source*
  '((defclass counter () ((value :initform 0 :accessor counter-value)))
    (defgeneric advance (counter))
    (defmethod advance ((counter counter)) (incf (counter-value counter)))
    (defun new-counter () (make-instance 'counter))
    (defun tick (counter) (advance counter))))

(let* ((unit (snowgrave:close-source-unit
              (list :forms *source*)
              :unit-name :counter
              :entries '(new-counter tick)
              :external-domains '((new-counter ()) (tick (counter)))))
       (counter (funcall (snowgrave:unit-function unit 'new-counter)))
       (tick (snowgrave:unit-function unit 'tick)))
  (assert (typep counter 'structure-object))
  (assert (= 1 (funcall tick counter)))
  (assert (= 2 (funcall tick counter)))
  ;; Bind this particular counter. Its value remains mutable; no component
  ;; role declarations are needed because this example has no component edges.
  (let ((bound-tick (snowgrave:bind-entry unit 'tick (list counter))))
    (assert (= 3 (funcall bound-tick)))
    (assert (= 4 (funcall bound-tick))))
  (format t "Closed counter: 1, 2; bound counter: 3, 4.~%"))
