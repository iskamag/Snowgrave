(defpackage #:snowgrave.annotation.fixture (:use #:cl))
(in-package #:snowgrave.tests)

(defun annotation-observation (function input events-reader)
  (handler-case
      (let ((values (multiple-value-list (funcall function input))))
        (list :values values (copy-list (funcall events-reader))))
    (type-error (condition)
      (list :type-error (class-name (class-of condition))
            (type-error-datum condition) (type-error-expected-type condition)
            (copy-list (funcall events-reader))))))

(defun annotation-loop-tests ()
  (let* ((*package* (find-package :snowgrave.annotation.fixture))
         (forms (read-from-string
                 "((defparameter *events* nil)
                   (defun in-loop (input)
                     (setf *events* nil)
                     (values (loop for item in (progn (push :source *events*) input)
                                   collect item)
                             (reverse *events*)))
                   (defun on-loop (input)
                     (setf *events* nil)
                     (values (loop for tail on (progn (push :source *events*) input)
                                   collect (car tail))
                             (reverse *events*)))
                   (defun annotation-values (input)
                     (setf *events* nil)
                     (multiple-value-bind (primary secondary)
                         (sb-kernel:the* (list :use-annotations t
                                              :source-form (error \"Metadata is not executable.\"))
                           (progn (push :once *events*) (values input :kept)))
                       (values primary secondary (reverse *events*))))
                   (defun read-events () (reverse *events*)))"))
         (entries (mapcar #'intern '("IN-LOOP" "ON-LOOP" "ANNOTATION-VALUES" "READ-EVENTS")))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(host-annotation-loops :version 1)
                :universe '(t list vector symbol integer)
                :entries entries
                :external-domains
                (mapcar (lambda (name)
                          (list name (if (eq name (fourth entries)) nil '(t))))
                        entries))))
    (dolist (form forms) (eval form))
    (let ((native-events (fdefinition (fourth entries)))
          (closed-events (snowgrave:unit-function unit (fourth entries))))
      ;; ON terminates on an atom without asserting LIST. IN leaves its actual
      ;; ENDP check in place, after the list expression's original effects.
      (dolist (entry (subseq entries 0 2))
        (dolist (input (list nil '(1 2 3) '(1 . 2) 17))
          (check (equal (annotation-observation (fdefinition entry) input native-events)
                        (annotation-observation (snowgrave:unit-function unit entry) input closed-events)))))
      ;; USE-ANNOTATIONS neither checks LIST nor loses secondary values.
      ;; Both the third returned value and the reader inspect this backend's
      ;; own global, including its effects before an original type error.
      (dolist (input (list 17 nil '(1 2) #(1 2)))
        (check (equal (annotation-observation (fdefinition (third entries)) input native-events)
                      (annotation-observation (snowgrave:unit-function unit (third entries)) input closed-events)))))))

(defun annotation-refusal-tests ()
  (let ((*package* (find-package :snowgrave.annotation.fixture)))
    (loop for (body feature) in
          '(("(coerce (sb-kernel:the* (list :use-annotations t) input) 'vector)"
             :coerce-sequence-domain)
            ("(sb-kernel:the* (integer) input)" :host-annotation-options)
            ("(sb-kernel:the* (integer :context :checked-value) input)" :host-annotation-options)
            ("(sb-kernel:the* (list :use-annotations t :context :annotation) input)" :host-annotation-options)
            ("(sb-kernel:the* (list :derive-type-only t) input)" :host-annotation-options)
            ("(sb-kernel:the* (list :truly t) input)" :host-annotation-options)
            ("(sb-kernel:the* (list :use-annotations t :restart t) input)" :host-annotation-options)
            ("(sb-kernel:the* (unadmitted-type :use-annotations t) input)" :host-annotation-type)
            ("(sb-kernel:the* (list :use-annotations) input)" :host-macroexpansion)
            ("(sb-kernel:the* list input)" :host-macroexpansion)
            ("(sb-kernel:the* (list :bogus t) input)" :host-macroexpansion)
            ("(sb-kernel:the* (list :use-annotations t) input input)" :host-macroexpansion))
          for index from 1 do
      (let* ((identity (list 'host-annotation-refusal :case index))
             (entry (intern "ENTRY"))
             (condition
               (handler-case
                   (progn
                     (snowgrave:close-source-unit
                      (list :forms (list (read-from-string (format nil "(defun entry (input) ~A)" body))))
                      :unit-name identity :universe '(t list vector symbol integer)
                      :entries (list entry) :external-domains (list (list entry '(t))))
                     nil)
                 (snowgrave:snowgrave-error (condition) condition))))
        (check (typep condition 'snowgrave:snowgrave-error))
        (check (eq feature (snowgrave:error-feature condition)))
        (check (equal (list identity 1) (snowgrave:error-source-key condition)))))))

(defun annotation-restart-refusal-tests ()
  ;; Actual SBCL THE* preserves secondary values on the valid path. Its walker
  ;; RESTART expansion captures only the primary value, so it is not admitted.
  (let* ((*package* (find-package :snowgrave.annotation.fixture))
         (form (read-from-string
                "(defun restart-values (input)
                   (sb-kernel:the* (list :restart t :context :annotation-test)
                     (values input :secondary)))"))
         (entry (second form))
         (identity '(host-annotation-restart :version 1)))
    (eval form)
    (check (equal '((:valid) :secondary)
                  (multiple-value-list (funcall entry '(:valid)))))
    (let ((condition
            (handler-case
                (progn
                  (snowgrave:close-source-unit
                   (list :forms (list form)) :unit-name identity :universe '(t list)
                   :entries (list entry) :external-domains (list (list entry '(list))))
                  nil)
              (snowgrave:snowgrave-error (condition) condition))))
      (check (typep condition 'snowgrave:snowgrave-error))
      (check (eq :host-annotation-options (snowgrave:error-feature condition)))
      (check (equal (list identity 1) (snowgrave:error-source-key condition))))))

(defun annotation-form-tests ()
  (annotation-loop-tests)
  (annotation-refusal-tests)
  (annotation-restart-refusal-tests))
