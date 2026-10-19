(defpackage #:snowgrave.local-flow.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass))
(in-package #:snowgrave.tests)

(defvar snowgrave.local-flow.fixture::*events* nil)
(defvar *local-flow-unit-sequence* 0)
(cl:defclass snowgrave.local-flow.fixture::marker () ())
(defun snowgrave.local-flow.fixture::opaque ()
  (make-instance 'snowgrave.local-flow.fixture::marker))
(defun snowgrave.local-flow.fixture::note (event)
  (push event snowgrave.local-flow.fixture::*events*) nil)
(defun snowgrave.local-flow.fixture::keyop (item)
  (if (typep item 'snowgrave.local-flow.fixture::marker) 1 0))

(defun local-flow-forms (body helpers)
  (let ((*package* (find-package :snowgrave.local-flow.fixture)))
    (read-from-string
     (format nil "((defclass marker () ()) ~A (defun entry () ~A))" helpers body))))
(defun close-local-flow (forms name)
  (let ((*package* (find-package :snowgrave.local-flow.fixture)))
    (snowgrave:close-source-unit
     (list :forms forms) :unit-name (list 'local-function-flow name (incf *local-flow-unit-sequence*))
     :closed-classes (list (intern "MARKER"))
     :universe (read-from-string "(marker integer number symbol list t)")
     :entries (list (intern "ENTRY")) :external-domains (list (list (intern "ENTRY") nil))
     :external-operations (mapcar #'intern '("OPAQUE" "NOTE" "KEYOP")))))
(defun check-local-flow (name body expected &key refuse
                                               (refusal-feature :external-result-class-observation)
                                               (helpers "(defun global-produce () 17)") events)
  (let ((forms (local-flow-forms body helpers)))
    (dolist (form forms) (eval form))
    (setf snowgrave.local-flow.fixture::*events* nil)
    (let ((native (multiple-value-list (funcall 'snowgrave.local-flow.fixture::entry)))
          (native-events nil))
      (setf native-events (reverse snowgrave.local-flow.fixture::*events*))
      (check (equal expected native))
      (check (equal events native-events))
      (if refuse
          (let ((condition (handler-case (progn (close-local-flow forms name) nil)
                             (snowgrave:snowgrave-error (condition) condition))))
            (check (typep condition 'snowgrave:unclosed-call))
            (check (eq refusal-feature (snowgrave:error-feature condition))))
          (let ((unit (close-local-flow forms name)))
            (setf snowgrave.local-flow.fixture::*events* nil)
            (check (equal native (multiple-value-list
                                 (funcall (snowgrave:unit-function unit 'snowgrave.local-flow.fixture::entry)))))
            (check (equal native-events (reverse snowgrave.local-flow.fixture::*events*))))))))

(defun local-function-flow-tests ()
  ;; Direct, literal indirect, and immutable local aliases share one actual
  ;; lexical return owner. Native record returns remain logical records.
  (dolist (call '("(produce)" "(funcall #'produce)" "(let ((saved #'produce)) (funcall saved))"))
    (check-local-flow (list 'opaque-producer call)
                      (format nil "(flet ((produce () (opaque))) (typep ~A 'marker))" call) '(t) :refuse t)
    (check-local-flow (list 'clean-scalar call)
                      (format nil "(flet ((produce () (values 17 :tag))) ~A)" call) '(17 :tag))
    (check-local-flow (list 'clean-record call)
                      (format nil "(flet ((produce () (make-instance 'marker))) (typep ~A 'marker))" call) '(t)))
  (check-local-flow 'secondary-local-origin
                    "(flet ((produce () (values nil (opaque))))
                       (multiple-value-bind (first second) (funcall #'produce)
                         (declare (ignore first)) (typep second 'marker)))" '(t) :refuse t)
  ;; Escapes from nested local bodies belong to the surrounding block's
  ;; result even when their ordinary call sites contain no RETURN-FROM.
  (check-local-flow 'nested-local-nonlocal-origin
                    "(typep (block done
                              (let ((held (opaque)))
                                (flet ((outer ()
                                         (flet ((escape () (return-from done held))) (escape) 17)))
                                  (outer) 17))) 'marker)" '(t) :refuse t)
  (check-local-flow 'nested-local-clean-nonlocal-return
                    "(block done
                       (flet ((outer ()
                                (flet ((escape () (return-from done 17))) (escape) 23)))
                         (outer) 23))" '(17))
  (check-local-flow 'captured-value-under-shadow
                    "(let ((held (opaque))) (flet ((produce () held))
                       (let ((held 17)) (declare (ignore held)) (typep (produce) 'marker))))" '(t) :refuse t)
  (check-local-flow 'clean-value-under-opaque-shadow
                    "(let ((held 17)) (flet ((produce () held))
                       (let ((held (opaque))) (declare (ignore held)) (produce))))" '(17))
  (check-local-flow 'saved-local-under-function-shadow
                    "(flet ((produce () (opaque))) (let ((saved #'produce))
                       (flet ((produce () 17)) (typep (funcall saved) 'marker))))" '(t) :refuse t)
  (check-local-flow 'saved-clean-under-opaque-shadow
                    "(flet ((produce () 17)) (let ((saved #'produce))
                       (flet ((produce () (opaque))) (funcall saved))))" '(17))
  (dolist (defaultp '(nil t))
    (let ((relay (if defaultp "(relay (&optional (payload (global-produce))) payload)"
                             "(relay () (global-produce))")))
      (check-local-flow (list 'flet-definitions-use-outer defaultp)
                        (format nil "(flet ((global-produce () 17) ~A) (typep (relay) 'marker))" relay)
                        '(t) :refuse t :helpers "(defun global-produce () (opaque))")
      (check-local-flow (list 'labels-definitions-use-peers defaultp)
                        (format nil "(labels ((global-produce () 17) ~A) (typep (relay) 'marker))" relay)
                        '(nil) :helpers "(defun global-produce () (opaque))")))
  (check-local-flow 'captured-optional-default
                    "(let ((held (opaque)))
                       (flet ((produce (&optional (payload held)) payload)) (typep (produce) 'marker)))" '(t) :refuse t)
  (check-local-flow 'ltv-null-env-opaque-global
                    "(flet ((global-produce () 17))
                       (typep (funcall (load-time-value #'global-produce)) 'marker))"
                    '(t) :refuse t :helpers "(defun global-produce () (opaque))")
  (check-local-flow 'ltv-null-env-clean-global
                    "(flet ((global-produce () (opaque))) (funcall (load-time-value #'global-produce)))" '(17))
  (check-local-flow 'labels-recursive-origin
                    "(labels ((produce (n) (if (zerop n) (opaque) (produce (1- n)))))
                       (typep (produce 2) 'marker))" '(t) :refuse t)
  (check-local-flow 'labels-mutual-origin
                    "(labels ((produce (n) (if (zerop n) (opaque) (next (1- n))))
                               (next (n) (produce n))) (typep (produce 2) 'marker))" '(t) :refuse t)
  (check-local-flow 'labels-recursive-native-values
                    "(labels ((produce (n) (if (zerop n) (values 17 :tag) (produce (1- n))))) (produce 3))" '(17 :tag))
  (check-local-flow 'ordered-zero-and-multiple-values
                    "(flet ((none () (note :zero) (values))
                             (pair (value) (note value) (values value (1+ value))))
                       (multiple-value-prog1
                           (multiple-value-call #'values (none) (pair 17) (none) (pair 23))
                         (note :cleanup)))" '(17 18 23 24) :events '(:zero 17 :zero 23 :cleanup))
  ;; Callback argument and KEY-result owners both participate. Opaque origin
  ;; cannot disappear when KEY feeds TEST, even over a clean input sequence.
  (check-local-flow 'callback-key-to-test-origin
                    "(flet ((keyer (item) (declare (ignore item)) (opaque))
                             (probe (needle item) (declare (ignore needle)) (typep item 'marker)))
                       (not (null (find nil '(0) :key #'keyer :test #'probe))))" '(t) :refuse t)
  (check-local-flow 'callback-key-to-test-clean
                    "(flet ((keyer (item) (declare (ignore item)) 17)
                             (probe (needle item) (= needle item)))
                       (not (null (find 17 '(0) :key #'keyer :test #'probe))))" '(t))
  (check-local-flow 'ignored-opaque-local-key-input
                    "(flet ((keyer (item) (declare (ignore item)) 7))
                       (not (null (find 7 (list (opaque)) :key #'keyer))))" '(t))
  (check-local-flow 'ignored-opaque-global-key-input
                    "(not (null (find 7 (list (opaque)) :key #'keyer)))" '(t)
                    :helpers "(defun keyer (item) (declare (ignore item)) 7)")
  (check-local-flow 'mixed-clean-and-opaque-key-input
                    "(flet ((keyer (item) (declare (ignore item)) 7))
                       (values (not (null (find 7 '(0) :key #'keyer)))
                               (not (null (find 7 (list (opaque)) :key #'keyer)))))" '(t t))
  (check-local-flow 'mutable-list-preserves-opaque-element
                    "(let ((items (list (opaque)))) (push 17 items) (typep (second items) 'marker))"
                    '(t) :refuse t)
  (check-local-flow 'mapcar-callback-output-origin
                    "(flet ((produce (item) (declare (ignore item)) (opaque)))
                       (typep (car (mapcar #'produce '(0))) 'marker))" '(t) :refuse t)
  (check-local-flow 'reduce-callback-accumulator-origin
                    "(flet ((combine (acc item)
                              (if (eql item 0) (opaque) (typep acc 'marker))))
                       (reduce #'combine '(0 1) :initial-value nil))" '(t) :refuse t)
  (check-local-flow 'reduce-empty-callback-default-origin
                    "(flet ((combine (&optional (acc (opaque)) item) (declare (ignore item)) acc))
                       (typep (reduce #'combine nil) 'marker))" '(t) :refuse t)
  (check-local-flow 'reduce-empty-clean-callback-default
                    "(flet ((combine (&optional (acc 17) item) (declare (ignore item)) acc))
                       (reduce #'combine nil))" '(17))
  (check-local-flow 'qualified-external-callback-under-local-shadow
                    "(flet ((keyop (item) (declare (ignore item)) 1))
                       (not (null (find 1 (list (make-instance 'marker))
                                        :key (load-time-value #'keyop)))))"
                    '(t) :refuse t :refusal-feature :external-callback-representation)
  (check-local-flow 'clean-local-setf-function
                    "(flet (((setf local-cell) (value object) (declare (ignore object)) value))
                       (setf (local-cell (opaque)) 17))" '(17))
  (check-local-flow 'opaque-local-setf-function-input
                    "(flet (((setf local-cell) (value object) (declare (ignore value)) (typep object 'marker)))
                       (setf (local-cell (opaque)) 17))" '(t) :refuse t)
  (local-flow-underarity-tests)
  (check-local-flow 'literal-mapcar-callback-output-origin
                    "(typep (car (mapcar #'(lambda (item) (declare (ignore item)) (opaque)) '(0))) 'marker)"
                    '(t) :refuse t)
  (check-local-flow 'literal-mapcar-ignored-opaque-input
                    "(car (mapcar #'(lambda (item) (declare (ignore item)) 7) (list (opaque))))" '(7))
  ;; A saved anonymous closure has no owned definition-site capture receipt
  ;; in this bounded profile. Refuse instead of analysing its body under the
  ;; clean use-site shadow. Literal callbacks above remain admitted.
  (check-local-flow 'saved-anonymous-callback-capture-refusal
                    "(let ((held (opaque)))
                       (let ((callback #'(lambda (item) (declare (ignore item)) held)))
                         (let ((held 17)) (declare (ignore held))
                           (typep (car (mapcar callback '(0))) 'marker))))"
                    '(t) :refuse t :refusal-feature :callback-target)
  (check-local-flow 'saved-anonymous-funcall-capture-refusal
                    "(let ((held (opaque)))
                       (let ((callback #'(lambda () held)))
                         (let ((held 17)) (declare (ignore held)) (typep (funcall callback) 'marker))))"
                    '(t) :refuse t :refusal-feature :computed-function)
  ;; The already-admitted direct literal forms must project omitted defaults
  ;; through the same ordinary binder as local functions, including zero MVC
  ;; inputs. This is three paired controls, not a syntax cross-product.
  (dolist (spec '((:funcall "(funcall #'(lambda (&optional (payload ~A)) payload))")
                  (:apply "(apply #'(lambda (&optional (payload ~A)) payload) nil)")
                  (:values "(multiple-value-call #'(lambda (&optional (payload ~A)) payload) (values))")))
    (check-local-flow (list 'literal-optional-default-origin (first spec))
                      (format nil "(typep ~A 'marker)" (format nil (second spec) "(opaque)")) '(t) :refuse t)
    (check-local-flow (list 'literal-clean-optional-default (first spec))
                      (format nil (second spec) "17") '(17)))
  ;; An unknown syntactic APPLY tail can be empty. Default provenance joins
  ;; supplied-input uncertainty instead of being replaced by it.
  (dolist (kind '("&optional" "&key"))
    (check-local-flow (list 'variable-tail-omitted-default-origin kind)
                      (format nil "(let ((tail nil))
                                    (typep (apply #'(lambda (~A (payload (opaque))) payload) tail) 'marker))" kind)
                      '(t) :refuse t)
    (check-local-flow (list 'variable-tail-clean-omitted-default kind)
                      (format nil "(let ((tail nil))
                                    (apply #'(lambda (~A (payload 17)) payload) tail))" kind) '(17))))

(defun local-flow-underarity-tests ()
  ;; Keep lexical binding/error identity even when an underarity call has no
  ;; normal result. The current host WARNING policy may cold-refuse static
  ;; bad arity; it must not prune the local into an undefined/global fallback.
  (dolist (call '("(local)" "(funcall #'local)"))
    (let ((forms (local-flow-forms
                  (format nil "(flet ((local (value) value)) ~A)" call)
                  "(defun global-produce () 17)")))
      (handler-bind ((style-warning #'muffle-warning))
        (dolist (form forms) (eval form)))
      (check (handler-case (progn (funcall 'snowgrave.local-flow.fixture::entry) nil)
               (program-error () t)))
      (let ((condition (handler-case (progn (close-local-flow forms (list 'local-underarity call)) nil)
                         (snowgrave:snowgrave-error (condition) condition))))
        (check (typep condition 'snowgrave:unsupported-definition))
        (check (eq :compiler-failure (snowgrave:error-feature condition)))
        (check (snowgrave:error-source-key condition))))))
