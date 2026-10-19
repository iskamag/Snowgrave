(defpackage #:snowgrave.native-results.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass))
(defpackage #:snowgrave.native-results.shadow
  (:use #:cl) (:shadow #:ash #:logand #:logior #:logxor #:lognot #:plusp #:length)
  (:shadowing-import-from #:snowgrave #:defclass))
(in-package #:snowgrave.tests)

(defvar snowgrave.native-results.fixture::*observed*)
(defun snowgrave.native-results.fixture::observe-shared ()
  (let ((value (svref snowgrave.native-results.fixture::*observed* 0)))
    (or (typep value 'standard-object) (functionp value))))

(defun native-result-observation (function reader input)
  ;; The caller and opaque observer hold the same real target vector. Each
  ;; backend's own reader observes its source global, also on the error path.
  (let* ((target (vector :untouched))
         (snowgrave.native-results.fixture::*observed* target))
    (handler-case
        (list :values (multiple-value-list (funcall function target input))
              (svref target 0) (funcall reader))
      (type-error (condition)
        (list :type-error (type-of condition) (type-error-datum condition)
              (type-error-expected-type condition) (svref target 0) (funcall reader))))))

(defun native-result-unit (operator syntax domain identity)
  (let* ((*package* (find-package :snowgrave.native-results.fixture))
         (two-arguments-p (member operator '(ash logand logior logxor)))
         (operand "(progn (push :operand *events*) input)")
         (count (format nil "(progn (push :count *events*) ~D)" (if (eq operator 'ash) -1 7)))
         (arguments (format nil "~A~@[ ~A~]" operand (when two-arguments-p count)))
         (call (ecase syntax
                 (:direct (format nil "(~A ~A)" operator arguments))
                 (:funcall (format nil "(funcall #'~A ~A)" operator arguments))
                 (:apply (if two-arguments-p
                             (format nil "(apply #'~A ~A (list ~A))" operator operand count)
                             (format nil "(apply #'~A (list ~A))" operator operand)))
                 (:values (format nil "(multiple-value-call #'~A (before) (produce input) (after))" operator))))
         (forms (read-from-string
                 (format nil
                  "((defclass holder () ())
                    (defparameter *events* nil)
                    (defun before () (push :before *events*) (values))
                    (defun produce (input) (push :produce *events*) (values input ~A))
                    (defun after () (push :after *events*) (values))
                    (defun read-events () (reverse *events*))
                    (defun entry (target input)
                      (setf *events* nil)
                      (unwind-protect
                          (let ((result ~A))
                            (setf (svref target 0) result)
                            (observe-shared)
                            (values result :kept))
                        (push :cleanup *events*))))"
                  (if two-arguments-p (if (eq operator 'ash) "-1" "7") "") call)))
         (entry (intern "ENTRY")) (reader (intern "READ-EVENTS"))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name identity
                :closed-classes (list (intern "HOLDER")) :universe (read-from-string "(holder number vector cons list symbol t)")
                :entries (list entry reader)
                :external-domains (list (list entry (list 'vector domain)) (list reader nil))
                :external-operations (list (intern "OBSERVE-SHARED")))))
    (dolist (form forms) (eval form))
    (values unit entry reader)))

(defun native-result-positive-tests ()
  (loop for (operator domain inputs) in
        '((ash t (33 -33 0 1/2 :bad))
          (logand t (33 -33 0 1/2 :bad))
          (logior t (33 -33 0 1/2 :bad))
          (logxor t (33 -33 0 1/2 :bad))
          (lognot t (33 -33 0 1/2 :bad))
          (plusp t (3 -2 0 #c(1 2) :bad))
          (length list (nil (1 2 3) (1 . 2)))
          (length vector (#(1 2))))
        do (dolist (syntax '(:direct :funcall :apply :values))
             (multiple-value-bind (unit entry reader)
                 (native-result-unit operator syntax domain (list 'native-scalar-result operator domain syntax))
               (dolist (input inputs)
                 (check (equalp
                         (native-result-observation (fdefinition entry) (fdefinition reader) input)
                         (native-result-observation (snowgrave:unit-function unit entry)
                                                    (snowgrave:unit-function unit reader) input))))
               (when (and (eq operator 'length) (eq domain 'vector))
                 (let ((input (make-array 5 :initial-element :data :fill-pointer 2 :adjustable t)))
                   (check (equalp
                           (native-result-observation (fdefinition entry) (fdefinition reader) input)
                           (native-result-observation (snowgrave:unit-function unit entry)
                                                      (snowgrave:unit-function unit reader) input)))))))))

(defun native-result-refusal-tests ()
  (let ((*package* (find-package :snowgrave.native-results.fixture)))
    ;; Successful scalar result facts cannot supply an input ABI for an open
    ;; host sequence. Direct and immediate indirect calls share that audit.
    (loop for (body feature) in
          '(("(length input)" :length-sequence-domain)
            ("(funcall #'length input)" :length-sequence-domain)
            ("(apply #'length (list input))" :length-sequence-domain)
            ("(multiple-value-call #'length (values input))" :length-sequence-domain)
            ("#'length" :ordinary-function-capture)
            ("(sb-kernel:ash-right input 1)" :call-target)
            ("(sb-kernel:two-arg-and input 7)" :call-target)
            ("(sb-kernel:two-arg-ior input 7)" :call-target)
            ("(sb-kernel:two-arg-xor input 7)" :call-target))
          for index from 1 do
      (let* ((identity (list 'native-length-refusal index))
             (entry (intern "ENTRY"))
             (condition
               (handler-case
                   (progn
                     (snowgrave:close-source-unit
                      (list :forms (list (read-from-string (format nil "(defun entry (input) ~A)" body))))
                      :unit-name identity :universe '(t vector list) :entries (list entry)
                      :external-domains (list (list entry '(t))))
                     nil)
                 (snowgrave:snowgrave-error (condition) condition))))
        (check (typep condition 'snowgrave:unclosed-call))
        (check (eq feature (snowgrave:error-feature condition)))
        (check (equal (list identity 1) (snowgrave:error-source-key condition)))))
    ;; Neither a record nor a relocated callable can be published into the
    ;; externally held vector, regardless of nearby scalar computations.
    (dolist (value '("(make-instance 'holder)" "#'entry"))
      (let* ((identity (list 'native-result-store-refusal value))
             (forms (read-from-string
                     (format nil "((defclass holder () ())
                                   (defun entry (target input)
                                     (ash 33 -1) (plusp 3) (length '(1 2))
                                     (setf (svref target 0) ~A)))" value)))
             (condition
               (handler-case
                   (progn
                     (snowgrave:close-source-unit
                      (list :forms forms) :unit-name identity
                      :closed-classes (list (intern "HOLDER")) :universe (read-from-string "(holder vector number t)")
                      :entries (list (intern "ENTRY"))
                      :external-domains (list (list (intern "ENTRY") '(vector t)))
                      :external-operations (list (intern "OBSERVE-SHARED")))
                     nil)
                 (snowgrave:snowgrave-error (condition) condition))))
        (check (typep condition 'snowgrave:unclosed-call))
        (check (eq :external-shared-state-representation (snowgrave:error-feature condition)))
        (check (equal (list identity 2) (snowgrave:error-source-key condition)))))))

(defun native-result-shadow-tests ()
  ;; User operations with the same printed names retain their actual meaning.
  ;; A local binding can return a record; its name does not imply a scalar.
  (let ((*package* (find-package :snowgrave.native-results.shadow)))
    (dolist (operator '("ASH" "LOGAND" "LOGIOR" "LOGXOR" "LOGNOT" "PLUSP" "LENGTH"))
      (let* ((identity (list 'native-result-shadow operator))
             (forms (read-from-string
                     (format nil "((defclass holder () ())
                                   (defun entry (target input)
                                     (flet ((~A (x) (declare (ignore x)) (make-instance 'holder)))
                                       (setf (svref target 0) (~A input)))))" operator operator)))
             (condition
               (handler-case
                   (progn
                     (snowgrave:close-source-unit
                      (list :forms forms) :unit-name identity
                      :closed-classes (list (intern "HOLDER")) :universe (read-from-string "(holder vector number t)")
                      :entries (list (intern "ENTRY"))
                      :external-domains (list (list (intern "ENTRY") '(vector t)))
                      :external-operations '(snowgrave.native-results.fixture::observe-shared))
                     nil)
                 (snowgrave:snowgrave-error (condition) condition))))
        (check (typep condition 'snowgrave:unclosed-call))
        (check (eq :external-shared-state-representation (snowgrave:error-feature condition)))
        (check (equal (list identity 2) (snowgrave:error-source-key condition)))))))

(defun filtered-sequence-result-tests ()
  (let ((*package* (find-package :snowgrave.native-results.fixture)))
    (dolist (operator '(remove delete))
      (dolist (domain '(list vector string))
        (dolist (syntax '(:direct :funcall :apply :values))
          (let* ((item (if (eq domain 'string) "#\\a" "1"))
                 (call (ecase syntax
                         (:direct (format nil "(~A ~A input)" operator item))
                         (:funcall (format nil "(funcall #'~A ~A input)" operator item))
                         (:apply (format nil "(apply #'~A ~A (list input))" operator item))
                         (:values (format nil "(multiple-value-call #'~A (values ~A input))" operator item))))
                 (form (read-from-string
                        (format nil "(defun entry (input) (let ((result ~A)) (values (length result) result)))" call)))
                 (entry (intern "ENTRY"))
                 (unit (snowgrave:close-source-unit
                        (list :forms (list form)) :unit-name (list 'filtered-sequence operator domain syntax)
                        :universe (list domain) :entries (list entry)
                        :external-domains (list (list entry (list domain))))))
            (eval form)
            (flet ((input () (ecase domain (list (list 1 2 1)) (vector (vector 1 2 1))
                                          (string (copy-seq "aba")))))
              (check (equalp (multiple-value-list (funcall entry (input)))
                             (multiple-value-list (funcall (snowgrave:unit-function unit entry) (input))))))))))
    (loop for (body feature) in
          '(("(length (remove nil (opaque)))" :length-sequence-domain)
            ("(length (funcall #'delete nil (opaque)))" :length-sequence-domain)
            ("(flet ((remove (x y) (declare (ignore x y)) (make-instance 'holder)))
                (length (remove nil (list 1 2))))" :length-sequence-domain)
            ("(setf (svref target 0) (remove nil (list (make-instance 'holder))))"
             :external-shared-state-representation)
            ("(setf (svref target 0) (funcall #'delete nil (list #'entry)))"
             :external-shared-state-representation))
          for index from 0 do
      (let* ((forms (read-from-string
                     (format nil "((defclass holder () ()) (defun entry (target) ~A))" body)))
             (entry (intern "ENTRY"))
             (condition
               (handler-case
                   (progn
                     (snowgrave:close-source-unit
                      (list :forms forms) :unit-name (list 'filtered-sequence-refusal index)
                      :closed-classes (list (intern "HOLDER")) :universe (list (intern "HOLDER") 'vector 't)
                      :entries (list entry) :external-domains (list (list entry '(vector)))
                      :external-operations (list (intern "OPAQUE"))) nil)
                 (snowgrave:snowgrave-error (condition) condition))))
        (check (typep condition 'snowgrave:unclosed-call))
        (check (eq feature (snowgrave:error-feature condition)))))))

(defun native-aggregate-result-tests ()
  (native-result-positive-tests)
  (native-result-refusal-tests)
  (native-result-shadow-tests)
  (filtered-sequence-result-tests))
