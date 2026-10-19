(defpackage #:snowgrave.lambda-origin.fixture
  (:use #:cl)
  (:shadowing-import-from #:snowgrave #:defclass #:defgeneric #:defmethod))
(in-package #:snowgrave.tests)
(cl:defclass snowgrave.lambda-origin.fixture::marker () ())
(defun snowgrave.lambda-origin.fixture::opaque ()
  (make-instance 'snowgrave.lambda-origin.fixture::marker))
(defun snowgrave.lambda-origin.fixture::opaque-tail ()
  (list (snowgrave.lambda-origin.fixture::opaque)))
(defun snowgrave.lambda-origin.fixture::opaque-key-tail ()
  (list :value (snowgrave.lambda-origin.fixture::opaque)))

(defun lambda-origin-call (kind syntax &optional cleanp)
  (let* ((value (if cleanp "17" "(opaque)"))
         (extras (if (eq kind :key) (format nil ":value ~A" value) value))
         (tail (if cleanp
                   (if (eq kind :key) "(list :value 17)" "(list 17)")
                   (if (eq kind :key) "(opaque-key-tail)" "(opaque-tail)"))))
    (ecase syntax
      (:direct (format nil "(forward 0 ~A)" extras))
      (:funcall (format nil "(funcall #'forward 0 ~A)" extras))
      (:apply (format nil "(apply #'forward 0 ~A)" tail))
      (:values (format nil "(multiple-value-call #'forward (values) (values 0 ~A))" extras)))))

(defun lambda-origin-forms (kind syntax mode genericp)
  (let* ((*package* (find-package :snowgrave.lambda-origin.fixture))
         (lambda-list (ecase kind (:rest "(x &rest tail)")
                                 (:optional "(x &optional value)") (:key "(x &key value)")))
         (value (if (eq kind :rest) "(car tail)" "value"))
         (body (ecase mode
                 (:return value)
                 (:observe (format nil "(typep ~A 'marker)" value))
                 (:clean (if (eq kind :rest) "(values (car tail) (length tail))" "(values value :tag)"))
                 (:ignore "7")))
         (call (lambda-origin-call kind syntax (eq mode :clean))))
    (read-from-string
     (format nil "((defclass marker () ()) ~A
                    (~A forward ~A (declare (ignore x)) ~A)
                    (defun entry () ~A))"
             (if genericp (format nil "(defgeneric forward ~A)" lambda-list) "")
             (if genericp "defmethod" "defun") lambda-list body
             (if (eq mode :return) (format nil "(typep ~A 'marker)" call) call)))))

(defun close-lambda-origin (forms identity &key genericp entry-domain)
  (let* ((*package* (find-package :snowgrave.lambda-origin.fixture))
         (entry (intern "ENTRY")) (forward (intern "FORWARD")))
    (snowgrave:close-source-unit
     (list :forms forms) :unit-name identity
     :closed-classes (list (intern "MARKER")) :closed-generics (when genericp (list forward))
     :universe (read-from-string "(marker t number list symbol)")
     :entries (if entry-domain (list entry forward) (list entry))
     :external-domains (append (list (list entry nil)) (when entry-domain (list (list forward (list entry-domain)))))
     :external-operations (mapcar #'intern '("OPAQUE" "OPAQUE-TAIL" "OPAQUE-KEY-TAIL")))))

(defun eval-lambda-origin-forms (forms)
  ;; Alternate ordinary/generic fixtures without retaining old method sets.
  (fmakunbound 'snowgrave.lambda-origin.fixture::forward)
  (dolist (form forms) (eval form)))

(defun entry-default-origin-tests ()
  (let ((*package* (find-package :snowgrave.lambda-origin.fixture)))
    (dolist (kind '(:optional :key))
      (dolist (helperp '(nil t))
        (dolist (mode '(:observe :ignore :clean))
          (let* ((default (if (eq mode :clean) "17" "(opaque)"))
                 (initializer (if helperp "(produce)" default))
                 (body (if (eq mode :ignore) "(declare (ignore payload)) (values 7 :ignored)"
                           "(typep payload 'marker)"))
                 (forms (read-from-string
                         (format nil "((defclass marker () ())
                                        (defun entry (~A (payload ~A)) ~A) ~A)"
                                 (if (eq kind :optional) "&optional" "&key") initializer body
                                 (if helperp (format nil "(defun produce () ~A)" default) ""))))
                 (identity (list 'entry-default-origin kind helperp mode)))
            (eval-lambda-origin-forms forms)
            (if (eq mode :observe)
                (let ((condition (handler-case (progn (close-lambda-origin forms identity) nil)
                                   (snowgrave:snowgrave-error (condition) condition))))
                  (check (funcall (intern "ENTRY")))
                  (check (typep condition 'snowgrave:unclosed-call))
                  (check (eq :external-result-class-observation (snowgrave:error-feature condition))))
                (let ((unit (close-lambda-origin forms identity)))
                  (check (equal (multiple-value-list (funcall (intern "ENTRY")))
                                (multiple-value-list (funcall (snowgrave:unit-function unit (intern "ENTRY"))))))))))))))

(defun captured-default-origin-tests ()
  (let ((*package* (find-package :snowgrave.lambda-origin.fixture)))
    (dolist (localp '(nil t))
      (dolist (kind '(:optional :key))
        (dolist (mode '(:observe :ignore :clean))
          (let* ((lambda-list (format nil "(~A (payload ~A))"
                                      (if (eq kind :optional) "&optional" "&key")
                                      (if (eq mode :clean) "17" "(opaque)")))
                 (body (ecase mode (:observe "(typep payload 'marker)")
                                    (:ignore "(declare (ignore payload)) (values 7 :ignored)")
                                    (:clean "(values payload :clean)")))
                 (forms (read-from-string
                         (if localp
                             (format nil "((defclass marker () ())
                                            (defun entry () (flet ((forward ~A ~A)) #'forward)))"
                                     lambda-list body)
                             (format nil "((defclass marker () ()) (defun forward ~A ~A)
                                            (defun entry () #'forward))" lambda-list body))))
                 (identity (list 'captured-default-origin localp kind mode)))
            (eval-lambda-origin-forms forms)
            (if (eq mode :observe)
                (let ((condition (handler-case (progn (close-lambda-origin forms identity) nil)
                                   (snowgrave:snowgrave-error (condition) condition))))
                  (check (funcall (funcall (intern "ENTRY"))))
                  (check (typep condition 'snowgrave:unclosed-call))
                  (check (eq :external-result-class-observation (snowgrave:error-feature condition))))
                (let ((unit (close-lambda-origin forms identity)))
                  (check (equal (multiple-value-list (funcall (funcall (intern "ENTRY"))))
                                (multiple-value-list
                                 (funcall (funcall (snowgrave:unit-function unit (intern "ENTRY")))))))))))))))

(defun lambda-opaque-input-tests ()
  (entry-default-origin-tests)
  (captured-default-origin-tests)
  (let ((*package* (find-package :snowgrave.lambda-origin.fixture)))
    ;; Returning the rest/optional/key value and observing it inside the
    ;; callee both require the same actual-input origin. Exercise ordinary
    ;; helpers and selected generic methods through the shared binder.
    (dolist (genericp '(nil t))
      (dolist (kind '(:rest :optional :key))
        (dolist (syntax '(:direct :funcall :apply :values))
          (dolist (mode '(:return :observe))
            (let* ((forms (lambda-origin-forms kind syntax mode genericp))
                   (condition nil))
              (eval-lambda-origin-forms forms)
              (check (funcall (intern "ENTRY")))
              (setf condition
                    (handler-case
                        (progn (close-lambda-origin forms (list 'opaque-lambda-input genericp kind syntax mode)
                                                   :genericp genericp) nil)
                      (snowgrave:snowgrave-error (condition) condition)))
              (check (typep condition 'snowgrave:unclosed-call))
              (check (member (snowgrave:error-feature condition)
                             '(:external-result-class-observation :external-result-dispatch))))))))
    ;; A second public entry keeps its declared guard. An internal opaque
    ;; caller cannot borrow that nominal contract for optional/rest/key data.
    (dolist (domain '(integer t))
      (dolist (kind '(:rest :optional :key))
        (dolist (syntax '(:direct :funcall :apply :values))
          (let* ((forms (lambda-origin-forms kind syntax :return nil))
                 (condition
                   (handler-case
                       (progn (close-lambda-origin forms (list 'opaque-entry-input domain kind syntax)
                                                  :entry-domain domain) nil)
                     (snowgrave:snowgrave-error (condition) condition))))
            (check (typep condition 'snowgrave:unclosed-call))
            (check (eq :external-result-entry-argument (snowgrave:error-feature condition)))))))
    ;; Clean rest remains LIST, and named optional/key slots retain their
    ;; existing offsets. Native multiple values remain observable unchanged.
    (dolist (genericp '(nil t))
      (dolist (kind '(:rest :optional :key))
        (dolist (syntax '(:direct :funcall :apply :values))
          (let* ((forms (lambda-origin-forms kind syntax :clean genericp))
                 (unit (close-lambda-origin forms (list 'clean-lambda-input genericp kind syntax) :genericp genericp)))
            (eval-lambda-origin-forms forms)
            (check (equal (multiple-value-list (funcall (intern "ENTRY")))
                          (multiple-value-list (funcall (snowgrave:unit-function unit (intern "ENTRY"))))))
            (when (and (not genericp) (eq kind :rest))
              (let* ((flow (getf (snowgrave:unit-report unit) :ordinary-function-flow))
                     (row (find (snowgrave::function-name-key (intern "FORWARD")) (getf flow :functions)
                                :key (lambda (row) (getf row :function-key)) :test #'equal)))
                (check (eq 'list (getf row :rest-domain)))))))))
    ;; The tainted tuple is still a usable source input when the helper never
    ;; observes or returns it. Reflexive origin facts are not class proofs.
    (dolist (syntax '(:direct :funcall :apply :values))
      (let* ((forms (lambda-origin-forms :rest syntax :ignore nil))
             (unit (close-lambda-origin forms (list 'ignored-opaque-rest syntax))))
        (eval-lambda-origin-forms forms)
        (check (= 7 (funcall (intern "ENTRY")) (funcall (snowgrave:unit-function unit (intern "ENTRY")))))))))
