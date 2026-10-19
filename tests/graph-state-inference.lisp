(defpackage #:snowgrave.graph-state.fixture (:use #:cl))
(in-package #:snowgrave.tests)

(defvar *graph-state-test-sequence* 0)
(defun graph-state-forms (text)
  (let ((*package* (find-package :snowgrave.graph-state.fixture)))
    (read-from-string text)))
(defun graph-state-close (tag forms entries domains &key generics resources external)
  (let ((classes (loop for form in forms when (eq (car form) 'defclass) collect (second form))))
    (snowgrave:close-source-unit
     (list :forms forms) :unit-name (list :graph-state tag (incf *graph-state-test-sequence*))
     :closed-classes classes :closed-generics generics
     :universe (append classes '(number symbol vector list cons function t))
     :entries entries :external-domains domains :native-bindings resources
     :external-operations external)))
(defun graph-state-refuses (thunk &optional feature)
  (let ((condition (handler-case (progn (funcall thunk) nil)
                     (snowgrave:snowgrave-error (condition) condition))))
    (check (typep condition 'snowgrave:snowgrave-error))
    (when feature (check (eq feature (snowgrave:error-feature condition))))
    condition))
(defun graph-state-fixed (unit name)
  (snowgrave:unit-function unit name :bind-configuration t))

(defun graph-state-method-tests ()
  (let* ((*package* (find-package :snowgrave.graph-state.fixture))
         (forms (graph-state-forms
                 "((defclass provider () ((data :initarg :data :reader backing)))
                    (defclass action () ((provider :initarg :provider :reader provider)))
                    (defclass choice () ((action :initarg :action :reader action)))
                    (defclass unrelated () ((data :initarg :data :reader unused-reader)))
                    (defgeneric clear-provider (provider))
                    (defmethod clear-provider ((provider provider))
                      (length (fill (backing provider) nil)))
                    (defun relay (choice) (provider (action choice)))
                    (defun entry (root) (clear-provider (relay root))))")))
    (dolist (form forms) (eval form))
    (let* ((data (vector 17 23))
           (provider (make-instance (intern "PROVIDER") :data data))
           (action (make-instance (intern "ACTION") :provider provider))
           (root (make-instance (intern "CHOICE") :action action))
           (entry (intern "ENTRY"))
           (unit (graph-state-close
                  :method-chain forms (list entry) (list (list entry (list (list 'eql root))))
                  :generics (mapcar #'intern '("BACKING" "PROVIDER" "ACTION" "CLEAR-PROVIDER" "UNUSED-READER"))
                  :resources (list (list :backing data)))))
      ;; UNUSED-READER's selected unrelated cell remains in the admitted unit;
      ;; its ordinary slot condition cannot expose any captured private class.
      (check (= 2 (funcall (graph-state-fixed unit entry))))
      (check (every #'null data))
      (setf (aref data 0) 29)
      (check (= 2 (funcall (graph-state-fixed unit entry))))
      (check (every #'null data))
      (signals error (snowgrave:unit-function unit entry))))
  ;; A conservative base-class method cell overlaps the captured subclass.
  ;; It cannot borrow the disjoint-class proof or a particular bound node.
  (let* ((*package* (find-package :snowgrave.graph-state.fixture))
         (forms (graph-state-forms
                 "((defclass base () ((data :initarg :data)))
                    (defclass child (base) ())
                    (defgeneric uncalled-read (root))
                    (defmethod uncalled-read ((root base)) (slot-value root 'data))
                    (defun entry (root) (eq root root)))")))
    (dolist (form forms) (eval form))
    (let* ((root (make-instance (intern "CHILD") :data 17)) (entry (intern "ENTRY")))
      (graph-state-refuses
       (lambda () (graph-state-close :base-overlap forms (list entry)
                    (list (list entry (list (list 'eql root)))) :generics (list (intern "UNCALLED-READ"))))
       :graph-state-slot-read))))

(defun graph-state-equality-tests ()
  (let* ((*package* (find-package :snowgrave.graph-state.fixture))
         (forms (graph-state-forms
                 "((defclass node () ((next :initarg :next) (payload :initarg :payload)))
                    (defun entry (left right)
                      (values (equalp left right) (equal left right) (eq left right)
                              (equalp left left) (eq (slot-value left 'next) left)
                              (funcall #'equalp left right)
                              (multiple-value-call #'equalp (values left) (values right)))))")))
    (dolist (form forms) (eval form))
    (let* ((left (make-instance (intern "NODE") :payload 17))
           (right (make-instance (intern "NODE") :payload 17))
           (entry (intern "ENTRY")))
      (setf (slot-value left (intern "NEXT")) left
            (slot-value right (intern "NEXT")) right)
      (let* ((native (multiple-value-list (funcall entry left right)))
             (unit (graph-state-close :equality forms (list entry)
                    (list (list entry (list (list 'eql left) (list 'eql right)))))))
        (check (equal '(nil nil nil t t nil nil) native))
        (check (equal native (multiple-value-list (funcall (graph-state-fixed unit entry)))))))))

(defun graph-state-noescape-tests ()
  (let* ((*package* (find-package :snowgrave.graph-state.fixture))
         (base (first (graph-state-forms "((defclass holder () ((data :initarg :data))))")))
         (entry (intern "ENTRY")))
    (dolist (body '("root" "(values 17 root)" "(list root)"
                    "(progn (fill (vector root) nil :end (slot-value root 'data)) 0)"
                    "(progn (error \"state ~S\" root) 0)"
                    "(throw 'outside root)"
                    "(let ((array (vector nil))) (setf (aref array 0) root) 0)"
                    "(make-instance 'holder :data root)"
                    "#'(lambda () root)"))
      (let* ((form (first (graph-state-forms (format nil "((defun entry (root) ~A))" body))))
             (forms (list base form)))
        (dolist (definition forms) (eval definition))
        (let ((root (make-instance (intern "HOLDER") :data 17)))
          (graph-state-refuses
           (lambda () (graph-state-close body forms (list entry)
                        (list (list entry (list (list 'eql root))))))
           (when (search "(fill (vector" body) :graph-state-operation-input)))))
    ;; Captured native containers could themselves become bounds-condition
    ;; receivers. Their closure must not contain a copied private record.
    (dolist (kind '(:vector :list))
      (let ((forms (list base (first (graph-state-forms "((defun entry (root) (eq root root)))")))))
        (dolist (definition forms) (eval definition))
        (let* ((root (make-instance (intern "HOLDER") :data nil))
               (container (ecase kind (:vector (vector root)) (:list (list root)))))
          (setf (slot-value root (intern "DATA")) container)
          (graph-state-refuses
           (lambda () (graph-state-close kind forms (list entry)
                        (list (list entry (list (list 'eql root)))))) :graph-state-container-closure))))
    ;; Globals and native operations are both observable authority boundaries.
    (dolist (kind '(:global :external))
      (let* ((extra (graph-state-forms
                     (ecase kind
                       (:global "((defvar *saved* nil) (defun entry (root) (setf *saved* root) 0))")
                       (:external "((defun expose (value) (declare (ignore value)) 0) (defun entry (root) (expose root)))"))))
             (forms (cons base extra)))
        (dolist (definition forms) (eval definition))
        (let ((root (make-instance (intern "HOLDER") :data 17)))
          (graph-state-refuses
           (lambda () (graph-state-close kind forms (list entry)
                        (list (list entry (list (list 'eql root))))
                        :external (when (eq kind :external) (list (intern "EXPOSE")))))))))))

(defun graph-state-preservation-tests ()
  (let* ((*package* (find-package :snowgrave.graph-state.fixture))
         (base (first (graph-state-forms "((defclass holder () ((data :initarg :data))))")))
         (clear (first (graph-state-forms "((defun entry (root) (length (fill (slot-value root 'data) nil))))")))
         (entry (intern "ENTRY")) (mutate (intern "MUTATE")))
    (dolist (body '("(setf (slot-value root 'data) 17)" "(slot-makunbound root 'data)"))
      (let* ((mutation (first (graph-state-forms (format nil "((defun mutate (root) ~A))" body))))
             (forms (list base clear mutation)))
        (dolist (definition forms) (eval definition))
        (let* ((data (vector 17)) (root (make-instance (intern "HOLDER") :data data))
               (domains (list (list entry (list (list 'eql root))) (list mutate (list (list 'eql root))))))
          (graph-state-refuses
           (lambda () (graph-state-close body forms (list entry mutate) domains :resources (list (list :data data))))))))
    (let ((forms (list base clear)))
      ;; A nominal class entry still proves neither initial boundness nor
      ;; native backing shape. The new facility requires actual fixed roots.
      (graph-state-refuses
       (lambda () (graph-state-close
                    :class-only
                    (list base (first (graph-state-forms
                                       "((defun entry (root) (fill (slot-value root 'data) nil) 0))")))
                    (list entry) (list (list entry (list (intern "HOLDER")))))) :fill-sequence-domain)
      (dolist (definition forms) (eval definition))
      (let ((root (make-instance (intern "HOLDER"))))
        (graph-state-refuses
         (lambda () (graph-state-close :unbound forms (list entry)
                      (list (list entry (list (list 'eql root)))))))))
    ;; Shape of an imported pointer array does not classify its elements.
    (let* ((observe (first (graph-state-forms
                           "((defun entry (root) (typep (aref (slot-value root 'data) 0) 'holder)))")))
           (forms (list base observe)))
      (dolist (definition forms) (eval definition))
      (let* ((data (vector nil)) (root (make-instance (intern "HOLDER") :data data)))
        (graph-state-refuses
         (lambda () (graph-state-close :opaque-element forms (list entry)
                      (list (list entry (list (list 'eql root)))) :resources (list (list :data data))))
         :external-result-class-observation)))))

(defvar *graph-state-effects* nil)
(defun graph-state-condition-tests ()
  (let* ((*package* (find-package :snowgrave.graph-state.fixture))
         (observe (intern "OBSERVE"))
         (forms (graph-state-forms
                 "((defclass bounded () ((data :initarg :data) (end :initarg :end)))
                    (defun entry (root)
                      (observe :before)
                      (unwind-protect
                           (progn (fill (slot-value root 'data) nil :end (slot-value root 'end)) 0)
                        (observe :cleanup))))")))
    (setf (fdefinition observe) (lambda (tag) (push tag *graph-state-effects*) nil))
    (dolist (form forms) (eval form))
    (let* ((native-data (vector 17)) (closed-data (vector 17))
           (native (make-instance (intern "BOUNDED") :data native-data :end 2))
           (captured (make-instance (intern "BOUNDED") :data closed-data :end 2))
           (entry (intern "ENTRY"))
           (unit (graph-state-close :condition forms (list entry)
                  (list (list entry (list (list 'eql captured))))
                  :resources (list (list :data closed-data)) :external (list observe))))
      (flet ((observation (function)
               (let ((*graph-state-effects* nil))
                 (handler-case (progn (funcall function) (error "Expected a bounds condition."))
                   (type-error (condition)
                     (list (type-of condition) (type-error-datum condition)
                           (type-error-expected-type condition) (reverse *graph-state-effects*)))))))
        (let ((expected (observation (lambda () (funcall entry native))))
              (actual (observation (graph-state-fixed unit entry))))
          (check (equal expected actual))
          (check (equal '(:before :cleanup) (fourth actual)))
          (check (equalp #(17) native-data))
          (check (equalp native-data closed-data)))))))

(defun graph-state-inference-tests ()
  (graph-state-method-tests)
  (graph-state-equality-tests)
  (graph-state-noescape-tests)
  (graph-state-preservation-tests)
  (graph-state-condition-tests))
