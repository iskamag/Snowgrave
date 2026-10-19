(defpackage #:snowgrave.cold-integer.shadow (:use #:cl) (:shadow #:min))
(in-package #:snowgrave.tests)

(defun cold-integer-initializer-tests ()
  (dolist (policy '(:selected :entries))
    (let* ((forms (deployment-forms
                   "((defconstant word-bits (min 32 (integer-length most-positive-fixnum)))
                      (defparameter *numbers*
                        (vector (+ 2 3) (- 3 7) (* 3 7) (1+ 2) (1- 2)
                                (min 8 4) (max 8 4) (abs -7) (mod -7 3) (rem -7 3)
                                (floor -7 3) (ceiling -7 3) (truncate -7 3) (round -7 3)
                                (ash 3 2) (logand 7 3) (logior 4 3) (logxor 7 3)
                                (lognot 0) (integer-length -8)))
                      (defun entry () (values word-bits *numbers*)))"))
           (expected (list (min 32 (integer-length most-positive-fixnum))
                           #(5 -4 21 3 1 4 8 7 2 -1 -3 -2 -2 -2 12 3 7 4 -1 3)))
           (unit (close-deployment forms :policy policy))
           (constants (getf (snowgrave:unit-metadata unit) :cold-integer-constants)))
      (check-deployment-parity unit forms expected)
      (check (equal constants (getf (snowgrave:unit-report unit) :cold-integer-constants)))
      (check (equal constants
                    (list (list :name-key (snowgrave::function-name-key 'most-positive-fixnum)
                                :host-value most-positive-fixnum))))
      (when (eq policy :entries) (deployment-fresh-test unit expected))))
  (let* ((forms (deployment-forms
                 "((defun entry () (load-time-value (min 32 (integer-length most-positive-fixnum)))))"))
         (unit (close-deployment forms)))
    (check-deployment-parity unit forms (list (min 32 (integer-length most-positive-fixnum)))))
  ;; INTEGER-LENGTH has the same ordinary/runtime admission as its checked
  ;; initializer use, including negative and bignum inputs.
  (let ((unit (snowgrave:close-source-unit
               (list :forms (deployment-forms "((defun entry (n) (integer-length n)))"))
               :unit-name (list :integer-length (incf *deployment-test-sequence*))
               :deployment-roots :entries :universe '(integer)
               :entries '(snowgrave.deployment.fixture::entry)
               :external-domains '((snowgrave.deployment.fixture::entry (integer))))))
    (dolist (n (list 0 -1 17 -17 (ash 1 200) (- (ash 1 200))))
      (check (= (integer-length n)
                (funcall (snowgrave:unit-function unit 'snowgrave.deployment.fixture::entry) n)))))
  ;; No mutable/global/foreign constant or floating environment is borrowed.
  (dolist (expression '("(min 32 *ambient*)" "(min 32 ambient-constant)"
                        "(min 32.0 7.0)" "(integer-length (get-universal-time))"
                        "(snowgrave.cold-integer.shadow::min 32 7)"))
    (deployment-refusal
     (deployment-forms (format nil "((defparameter *value* ~A) (defun entry () 17))" expression))
     :global-initializer))
  (let* ((forms (deployment-forms
                 "((defparameter *value* (integer-length 17)) (defun entry () *value*))"))
         (original (fdefinition 'integer-length)))
    (unwind-protect
         (sb-ext:without-package-locks
           (setf (fdefinition 'integer-length) (lambda (n) (funcall original n)))
           (deployment-refusal forms :global-initializer))
      (sb-ext:without-package-locks (setf (fdefinition 'integer-length) original))))
  ;; A source constant must not make cold cleanup mask the real close error.
  (let ((condition
          (deployment-refusal
           (deployment-forms "((defconstant word-bits 17) (defun entry () (get-universal-time)))")
           :call-target)))
    (check (= 2 (second (snowgrave:error-source-key condition)))))
  t)
