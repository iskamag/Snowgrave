(defpackage #:snowgrave.immediate-callee.fixture (:use #:cl))
(in-package #:snowgrave.tests)

(defun immediate-callee-positive-tests ()
  (let ((*package* (find-package :snowgrave.immediate-callee.fixture)))
    (loop for callee in
          '("(if flag #'measure #'other)"
            "(progn (push :callee *events*) (if flag #'measure #'other))"
            "(locally (declare (optimize speed)) (if flag #'measure #'other))"
            "(multiple-value-prog1 (if flag #'measure #'other) (push :callee *events*))"
            "(if flag (load-time-value #'measure) (load-time-value #'other))"
            "(progn (push :callee *events*)
                    (locally (if flag (multiple-value-prog1 #'measure (push :branch *events*)) #'other)))")
          for index from 1 do
      (dolist (syntax '(:funcall :apply :values))
        (let* ((call (ecase syntax
                       (:funcall (format nil "(funcall ~A (progn (push :argument *events*) (list 1 2 3)))" callee))
                       (:apply (format nil "(apply ~A (list (progn (push :argument *events*) (list 1 2 3))))" callee))
                       (:values (format nil "(multiple-value-call ~A (before)
                                             (values (progn (push :argument *events*) (list 1 2 3))))" callee))))
               (forms (read-from-string
                       (format nil
                        "((defparameter *events* nil)
                          (defun before () (push :before *events*) (values))
                          (defun measure (items) (push :measure *events*) (values (length items) :measure))
                          (defun other (items) (push :other *events*) (values (1+ (length items)) :other))
                          (defun entry (flag)
                            (setf *events* nil)
                            (multiple-value-bind (value marker) ~A
                              (values value marker (reverse *events*)))))" call)))
               (entry (intern "ENTRY"))
               (unit (snowgrave:close-source-unit
                      (list :forms forms) :unit-name (list 'immediate-callee index syntax)
                      :universe '(t list number vector) :entries (list entry)
                      :external-domains (list (list entry '(t))))))
          (dolist (form forms) (eval form))
          (dolist (flag '(nil t))
            (check (equal (multiple-value-list (funcall entry flag))
                          (multiple-value-list (funcall (snowgrave:unit-function unit entry) flag)))))))))
  ;; LOAD-TIME-VALUE retains its null lexical environment despite a local
  ;; function with the same user name surrounding the immediate callee.
  (let* ((*package* (find-package :snowgrave.immediate-callee.fixture))
         (forms (read-from-string
                 "((defun measure (items) (values (length items) :global))
                   (defun entry ()
                     (flet ((measure (items) (declare (ignore items)) (values 99 :local)))
                       (funcall (load-time-value #'measure) (list 1 2 3)))))"))
         (entry (intern "ENTRY"))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(immediate-callee-null-environment)
                :universe '(t list number) :entries (list entry) :external-domains (list (list entry nil)))))
    (dolist (form forms) (eval form))
    (check (equal '(3 :global) (multiple-value-list (funcall entry))))
    (check (equal '(3 :global) (multiple-value-list (funcall (snowgrave:unit-function unit entry)))))))

(defun immediate-callee-refusal-tests ()
  (let ((*package* (find-package :snowgrave.immediate-callee.fixture)))
    ;; References outside value-producing positions remain actual captures.
    ;; In particular, sharing one FUNCTION cons between value/effect/test
    ;; positions must not grant the other occurrence immediate-call privilege.
    (loop for body in
          '("(progn #'measure (funcall (if flag #'measure #'other) (list 1 2)))"
            "(funcall (progn (stash #'measure) (if flag #'measure #'other)) (list 1 2))"
            "(funcall (if (progn (stash #'measure) flag) #'measure #'other) (list 1 2))"
            "(funcall (multiple-value-prog1 #'measure (stash #'measure)) (list 1 2))"
            "(consume #'measure)"
            "#'measure"
            "(funcall (progn (stash #1=#'measure) #1#) (list 1 2))")
          for index from 1 do
      (let* ((identity (list 'immediate-callee-capture index))
             (forms (read-from-string
                     (format nil
                      "((defparameter *saved* nil)
                        (defun stash (callback) (setf *saved* callback))
                        (defun measure (items) (length items))
                        (defun other (items) (length items))
                        (defun consume (callback) (funcall callback (list 1 2)))
                        (defun entry (flag) ~A))" body)))
             (entry (intern "ENTRY"))
             (condition
               (handler-case
                   (progn
                     (snowgrave:close-source-unit
                      (list :forms forms) :unit-name identity :universe '(t list number)
                      :entries (list entry) :external-domains (list (list entry '(t))))
                     nil)
                 (snowgrave:snowgrave-error (condition) condition))))
        (check (typep condition 'snowgrave:unclosed-call))
        (check (eq :length-sequence-domain (snowgrave:error-feature condition)))
        (check (equal (list identity 3) (snowgrave:error-source-key condition)))))
    ;; LENGTH's immediate callable proof cannot be borrowed by any separate
    ;; occurrence, including an EQ-identical node in the authored source DAG.
    (loop for callee in
          '("(progn (stash #1=#'length) #1#)"
            "(if (progn (stash #1=#'length) flag) #1# #'length)"
            "(multiple-value-prog1 #1=#'length (stash #1#))")
          for index from 1 do
      (let* ((identity (list 'immediate-length-capture index))
             (forms (read-from-string
                     (format nil
                      "((defparameter *saved* nil)
                        (defun stash (callback) (setf *saved* callback))
                        (defun entry (flag) (funcall ~A (list 1 2))))" callee)))
             (entry (intern "ENTRY"))
             (condition
               (handler-case
                   (progn
                     (snowgrave:close-source-unit
                      (list :forms forms) :unit-name identity :universe '(t list number)
                      :entries (list entry) :external-domains (list (list entry '(t))))
                     nil)
                 (snowgrave:snowgrave-error (condition) condition))))
        (check (typep condition 'snowgrave:unclosed-call))
        (check (eq :ordinary-function-capture (snowgrave:error-feature condition)))
        (check (equal (list identity 3) (snowgrave:error-source-key condition)))))))

(defun immediate-callee-tests ()
  (immediate-callee-positive-tests)
  (immediate-callee-refusal-tests)
  (immediate-ltv-argument-scope-tests)
  (immediate-mapc-result-tests)
  (immediate-mapc-shadow-tests)
  (immediate-wrapped-ltv-tests))

(defun immediate-ltv-argument-scope-tests ()
  (let* ((*package* (find-package :snowgrave.immediate-callee.fixture))
         (forms (read-from-string
                 "((defun measure (items) (values (length items) (car items) :global))
                   (defun entry ()
                     (flet ((measure (ignored) (declare (ignore ignored)) 99))
                       (funcall (load-time-value #'measure) (list (measure nil))))))"))
         (entry (intern "ENTRY"))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(immediate-ltv-argument-scope)
                :universe '(t list number) :entries (list entry) :external-domains (list (list entry nil)))))
    (dolist (form forms) (eval form))
    (check (equal '(1 99 :global) (multiple-value-list (funcall entry))))
    (check (equal '(1 99 :global) (multiple-value-list (funcall (snowgrave:unit-function unit entry)))))))

(defun immediate-mapc-result-tests ()
  (let ((*package* (find-package :snowgrave.immediate-callee.fixture)))
    (loop for call in '("(mapc #'visit input)"
                       "(funcall #'mapc #'visit input)"
                       "(apply #'mapc (list #'visit input))"
                       "(multiple-value-call #'mapc (values #'visit) (values input))")
          for index from 1 do
      (let* ((forms (read-from-string
                     (format nil
                      "((defparameter *events* nil)
                        (defun visit (item) (push item *events*) nil)
                        (defun entry (input)
                          (setf *events* nil)
                          (let ((result ~A))
                            (values (eq result input) (length result) (reverse *events*)))))" call)))
             (entry (intern "ENTRY"))
             (unit (snowgrave:close-source-unit
                    (list :forms forms) :unit-name (list 'immediate-mapc-result index)
                    :universe '(t list number) :entries (list entry)
                    :external-domains (list (list entry '(list))))))
        (dolist (form forms) (eval form))
        (dolist (input '(nil (1 2 3)))
          (check (equal (list t (length input) input) (multiple-value-list (funcall entry input))))
          (check (equal (list t (length input) input)
                        (multiple-value-list (funcall (snowgrave:unit-function unit entry) input)))))))
    (eval (read-from-string "(defun external-list () (list 1 2 3))"))
    ;; MAPC returns the same opaque input object. A successful map does not
    ;; convert its origin into a proved native sequence ABI for LENGTH.
    (loop for call in '("(mapc #'identity (external-list))"
                       "(funcall #'mapc #'identity (external-list))"
                       "(apply #'mapc (list #'identity (external-list)))"
                       "(multiple-value-call #'mapc (values #'identity) (values (external-list)))")
          for index from 1 do
      (let* ((identity (list 'immediate-mapc-origin index))
             (entry (intern "ENTRY"))
             (forms (list (read-from-string (format nil "(defun entry () (length ~A))" call))))
             (condition
               (handler-case
                   (progn
                     (snowgrave:close-source-unit
                      (list :forms forms) :unit-name identity :universe '(t list number)
                      :entries (list entry) :external-domains (list (list entry nil))
                      :external-operations (list (intern "EXTERNAL-LIST")))
                     nil)
                 (snowgrave:snowgrave-error (condition) condition))))
        (check (typep condition 'snowgrave:unclosed-call))
        (check (eq :length-sequence-domain (snowgrave:error-feature condition)))
        (check (equal (list identity 1) (snowgrave:error-source-key condition)))))))

(defpackage #:snowgrave.immediate-callee.shadow (:use #:cl) (:shadow #:mapc))
(defun immediate-mapc-shadow-tests ()
  (let* ((*package* (find-package :snowgrave.immediate-callee.shadow))
         (forms (read-from-string
                 "((defun mapc (callback items)
                     (declare (ignore callback items)) (vector :different))
                   (defun entry (items) (length (mapc #'identity items))))"))
         (entry (intern "ENTRY"))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(immediate-mapc-user-name)
                :universe '(t list vector) :entries (list entry) :external-domains (list (list entry '(list))))))
    (dolist (form forms) (eval form))
    (check (= 1 (funcall entry '(1 2 3))))
    (check (= 1 (funcall (snowgrave:unit-function unit entry) '(1 2 3)))))
  (let* ((*package* (find-package :snowgrave.immediate-callee.shadow))
         (identity '(immediate-mapc-local-name))
         (entry (intern "ENTRY"))
         (forms (read-from-string
                 "((defun entry (items)
                     (flet ((mapc (callback input)
                              (declare (ignore callback input)) (vector :different)))
                       (length (mapc #'identity items)))))"))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name identity :universe '(t list vector)
                :entries (list entry) :external-domains (list (list entry '(list))))))
    ;; The lexical return owner proves this user function returns VECTOR;
    ;; it must not borrow CL:MAPC's input-list identity result contract.
    (dolist (form forms) (eval form))
    (check (= 1 (funcall entry '(1 2 3))))
    (check (= 1 (funcall (snowgrave:unit-function unit entry) '(1 2 3))))))

(defun immediate-wrapped-ltv-tests ()
  (let* ((*package* (find-package :snowgrave.immediate-callee.fixture))
         (forms (read-from-string
                 "((defun measure (items) (values (length items) (car items) :measure))
                   (defun other (items) (values (1+ (length items)) (car items) :other))
                   (defun entry (flag)
                     (flet ((measure (ignored) (declare (ignore ignored)) 99))
                       (funcall (if flag (load-time-value #'measure) (load-time-value #'other))
                                (list (measure nil))))))"))
         (entry (intern "ENTRY"))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(immediate-wrapped-ltv-owner)
                :universe '(t list number) :entries (list entry) :external-domains (list (list entry '(t))))))
    (dolist (form forms) (eval form))
    (dolist (flag '(nil t))
      (let ((expected (if flag '(1 99 :measure) '(2 99 :other))))
        (check (equal expected (multiple-value-list (funcall entry flag))))
        (check (equal expected (multiple-value-list (funcall (snowgrave:unit-function unit entry) flag)))))))
  (let* ((*package* (find-package :snowgrave.immediate-callee.fixture))
         (forms (read-from-string
                 "((defun measure (items) (length items))
                   (defun entry ()
                     (flet ((measure (ignored) (declare (ignore ignored)) 99))
                       (funcall #'measure (list 1 2 3)))))"))
         (entry (intern "ENTRY"))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(immediate-local-owner)
                :universe '(t list number) :entries (list entry) :external-domains (list (list entry nil)))))
    (dolist (form forms) (eval form))
    (check (= 99 (funcall entry)))
    (check (= 99 (funcall (snowgrave:unit-function unit entry)))))
  ;; A lexical FUNCTION in a mixed branch is not a qualified global identity.
  ;; The current value lattice refuses this unsupported finite local closure;
  ;; it must never audit or emit it as the unrelated global MEASURE function.
  (let* ((*package* (find-package :snowgrave.immediate-callee.fixture))
         (identity '(immediate-mixed-local-owner))
         (entry (intern "ENTRY"))
         (forms (read-from-string
                 "((defun measure (items) (length items))
                   (defun other (items) (length items))
                   (defun entry (flag)
                     (flet ((measure (ignored) (declare (ignore ignored)) 99))
                       (funcall (if flag #'measure (load-time-value #'other)) (list 1 2 3)))))"))
         (condition
           (handler-case
               (progn
                 (snowgrave:close-source-unit
                  (list :forms forms) :unit-name identity :universe '(t list number)
                  :entries (list entry) :external-domains (list (list entry '(t))))
                 nil)
             (snowgrave:snowgrave-error (condition) condition))))
    (check (typep condition 'snowgrave:unclosed-call))
    (check (eq :computed-function (snowgrave:error-feature condition)))
    (check (equal (list identity 3) (snowgrave:error-source-key condition)))))
