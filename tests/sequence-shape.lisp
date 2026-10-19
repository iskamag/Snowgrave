(defpackage #:snowgrave.sequence-shape.fixture (:use #:cl))
(defpackage #:snowgrave.sequence-shape.shadow (:use #:cl) (:shadow #:typep))
(in-package #:snowgrave.tests)

(defvar snowgrave.sequence-shape.fixture::*backing*)
(defvar snowgrave.sequence-shape.fixture::*events*)
(defun snowgrave.sequence-shape.fixture::opaque-sequence ()
  snowgrave.sequence-shape.fixture::*backing*)
(defun snowgrave.sequence-shape.fixture::observe (event)
  (push event snowgrave.sequence-shape.fixture::*events*) nil)

(defun sequence-shape-unit (body identity &key (parameters "()") domains helpers boot)
  (let* ((*package* (find-package :snowgrave.sequence-shape.fixture))
         (entry (intern "ENTRY"))
         (forms (read-from-string
                 (format nil "((defclass marker () ())
                               (defclass table () ((data :initarg :data)))
                               ~A ~A (defun entry ~A ~A))"
                         (if boot "(defun boot () (make-instance 'table :data (vector 1 2)))" "")
                         (or helpers "") parameters body)))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name identity
                :closed-classes (read-from-string "(marker table)")
                :universe (read-from-string "(marker table t vector list integer)")
                :entries (if boot (list entry (intern "BOOT")) (list entry))
                :external-domains (append (list (list entry domains)) (when boot (list (list (intern "BOOT") nil))))
                :external-operations (mapcar #'intern '("OPAQUE-SEQUENCE" "OBSERVE")))))
    (dolist (form forms) (eval form))
    (values unit (fdefinition entry))))

(defun sequence-shape-observation (function backing &rest arguments)
  ;; The opaque operation and the test retain the exact object. Do not observe
  ;; an independently copied or privately emitted global in place of it.
  (let ((snowgrave.sequence-shape.fixture::*backing* backing)
        (snowgrave.sequence-shape.fixture::*events* nil))
    (list (handler-case (list :values (multiple-value-list (apply function arguments)))
            (error (condition)
              (list :error (type-of condition)
                    (when (typep condition 'type-error)
                      (list (type-error-datum condition) (type-error-expected-type condition))))))
          backing (reverse snowgrave.sequence-shape.fixture::*events*))))

(defun sequence-shape-refuses (body feature &rest options)
  (let* ((identity (list 'sequence-shape-refusal body))
         (condition
           (handler-case
               (progn (apply #'sequence-shape-unit body identity options) nil)
             (snowgrave:snowgrave-error (condition) condition))))
    (check (typep condition 'snowgrave:snowgrave-error))
    (check (eq feature (snowgrave:error-feature condition)))
    (check (equal identity (first (snowgrave:error-source-key condition))))))

(defun sequence-shape-positive-tests ()
  (dolist (shape '(vector list))
    (dolist (syntax '(:direct :funcall :apply :values))
      (let* ((call (ecase syntax
                     (:direct "(fill data nil)")
                     (:funcall "(funcall #'fill data nil)")
                     (:apply "(apply #'fill data (list nil))")
                     (:values "(multiple-value-call #'fill (values data nil))")))
             (body (format nil "(let ((data (opaque-sequence)))
                                  (if (typep data '~A)
                                      (progn (observe :before)
                                        (multiple-value-prog1 (values (length ~A) :filled)
                                          (observe :after))) :not-sequence))" shape call)))
        (multiple-value-bind (unit native)
            (sequence-shape-unit body (list 'checked-sequence-fill shape syntax))
          (let* ((closed (snowgrave:unit-function unit "ENTRY"))
                 (backing (if (eq shape 'vector) (vector :a :b) (list :a :b)))
                 (observed (sequence-shape-observation closed backing)))
            (check (eq backing (second observed)))
            (check (equal '(nil nil) (coerce backing 'list)))
            (check (equal '(:before :after) (third observed)))
            (check (equal '(:values (2 :filled)) (first observed))))
          ;; Native cohort instances in externally aliased element positions
          ;; remain ordinary host values; FILL NIL needs no interpretation.
          (flet ((input ()
                   (let ((marker (make-instance 'snowgrave.sequence-shape.fixture::marker)))
                     (if (eq shape 'vector) (vector marker 17) (list marker 17)))))
            (check (equalp (sequence-shape-observation native (input))
                           (sequence-shape-observation (snowgrave:unit-function unit "ENTRY") (input)))))
          (check (equal '((:values (:not-sequence)) 17 nil)
                        (sequence-shape-observation (snowgrave:unit-function unit "ENTRY") 17)))))))
  ;; Bounds/type failure and cleanup remain owned by the actual host FILL.
  (multiple-value-bind (unit native)
      (sequence-shape-unit
       "(let ((data (opaque-sequence)))
          (if (typep data 'vector)
              (progn (observe :before)
                (unwind-protect (values (length (fill data nil :end end)) :filled)
                  (observe :cleanup))) :not-sequence))"
       '(checked-fill-failure) :parameters "(end)" :domains '(t))
    (dolist (end '(0 1 2 4 -1 :bad))
      (check (equalp (sequence-shape-observation native (vector :a :b) end)
                     (sequence-shape-observation (snowgrave:unit-function unit "ENTRY") (vector :a :b) end)))))
  ;; Geometry is carried through ordinary caller/return tuples and unions.
  (multiple-value-bind (unit native)
      (sequence-shape-unit
       "(let ((data (opaque-sequence)))
          (cond ((typep data 'vector) (fill-length data))
                ((typep data 'list) (fill-length data)) (t :not-sequence)))"
       '(checked-sequence-union)
       :helpers "(defun keep (data) (values data :kept))
                 (defun fill-length (data)
                   (multiple-value-bind (same tag) (keep data)
                     (values (length (fill same nil)) tag)))")
    (dolist (shape '(list vector))
      (flet ((input () (if (eq shape 'list) (list :a :b) (vector :a :b))))
        (check (equalp (sequence-shape-observation native (input))
                       (sequence-shape-observation (snowgrave:unit-function unit "ENTRY") (input)))))))
  ;; A helper reached by checked LIST and VECTOR callers must keep the union
  ;; through sequence-family results, rather than falling back to bare origin.
  ;; Its actual call supplies the FILL receiver once, in every admitted syntax.
  (loop for expression in '("(reverse data)" "(remove nil data)" "(delete nil data)")
        for index from 0 do
    (dolist (syntax '(:direct :funcall :apply :values))
      (let ((call (ecase syntax
                    (:direct "(fill (sequence-result data) nil)")
                    (:funcall "(funcall #'fill (sequence-result data) nil)")
                    (:apply "(apply #'fill (sequence-result data) (list nil))")
                    (:values "(multiple-value-call #'fill (values (sequence-result data) nil))"))))
        (multiple-value-bind (unit native)
            (sequence-shape-unit
             "(let ((data (opaque-sequence)))
                (cond ((typep data 'vector) (result-length data))
                      ((typep data 'list) (result-length data)) (t :not-sequence)))"
             (list 'checked-union-sequence-result index syntax)
             :helpers (format nil "(defun sequence-result (data) (observe :receiver) ~A)
                                   (defun result-length (data) (length ~A))" expression call))
          (dolist (shape '(list vector))
            (flet ((input () (if (eq shape 'list) (list :a :b) (vector :a :b))))
              (check (equalp (sequence-shape-observation native (input))
                             (sequence-shape-observation (snowgrave:unit-function unit "ENTRY") (input))))))))))
  ;; An empty literal APPLY tail remains an argument to APPLY, even though
  ;; the shared flattened source tuple contains no positions from that tail.
  (dolist (operator '(fill remove))
    (dolist (tail '("nil" "(list)"))
      (multiple-value-bind (unit native)
          (sequence-shape-unit
           (format nil "(let ((data (opaque-sequence))) (if (typep data 'vector)
                          (length (apply #'~A ~A ~A)) :not-sequence))" operator
                   (if (eq operator 'fill)
                       "(progn (observe :receiver) data) (progn (observe :value) nil)"
                       "(progn (observe :item) nil) (progn (observe :receiver) data)") tail)
           (list 'checked-empty-apply-tail operator tail))
        (check (equalp (sequence-shape-observation native (vector :a :b))
                       (sequence-shape-observation (snowgrave:unit-function unit "ENTRY") (vector :a :b)))))))
  ;; A proved LIST selects the host compiler's ordinary LIST-REVERSE leaf;
  ;; it retains elements/effects without entering extended-sequence dispatch.
  (dolist (call '("(reverse (progn (observe :receiver) data))"
                  "(funcall #'reverse (progn (observe :receiver) data))"
                  "(apply #'reverse (list (progn (observe :receiver) data)))"
                  "(multiple-value-call #'reverse (values (progn (observe :receiver) data)))"))
    (multiple-value-bind (unit native)
        (sequence-shape-unit
         (format nil "(let ((data (opaque-sequence))) (if (typep data 'list)
                        (length ~A) :not-sequence))" call)
         (list 'checked-list-reverse call))
      (check (equalp (sequence-shape-observation native (list :a :b))
                     (sequence-shape-observation (snowgrave:unit-function unit "ENTRY") (list :a :b))))))
  ;; Identity assertions and the existing sequence-result owner preserve
  ;; geometry independently of opaque element provenance.
  (loop for (expression shape) in
        '(("(the list data)" list)
          ("(mapc #'identity data)" list)
          ("(coerce data 'vector)" list)
          ("(reverse data)" vector)
          ("(remove nil data)" vector)
          ("(funcall #'delete nil data)" list))
        for index from 0 do
    (multiple-value-bind (unit native)
        (sequence-shape-unit
         (format nil "(let ((data (opaque-sequence))) (if (typep data '~A)
                        (length ~A) :not-sequence))" shape expression)
         (list 'checked-sequence-result index))
      (flet ((input () (if (eq shape 'list) (list :a :b) (vector :a :b))))
        (check (equalp (sequence-shape-observation native (input))
                       (sequence-shape-observation (snowgrave:unit-function unit "ENTRY") (input)))))))
  ;; A class alone does not establish a field's boundness or sequence shape.
  ;; This positive case depends on the actual TYPEP after the ordinary read.
  (multiple-value-bind (unit native)
      (sequence-shape-unit
       "(let ((data (slot-value owner 'data)))
          (if (typep data 'vector) (length (fill data nil)) :not-vector))"
       '(checked-slot-sequence) :parameters "(owner)"
       :domains '(snowgrave.sequence-shape.fixture::table) :boot t)
    (let ((native-owner (funcall 'snowgrave.sequence-shape.fixture::boot))
          (closed-owner (funcall (snowgrave:unit-function unit "BOOT"))))
      (check (= (funcall native native-owner)
                (funcall (snowgrave:unit-function unit "ENTRY") closed-owner))))))

(defun sequence-shape-origin-tests ()
  ;; Shape/result identities and admitted sequence operations retain origin.
  ;; Neither an empty fill nor a copying/filtering operation sanitizes elements.
  (loop for (expression shape) in
        '(("(fill data nil :end 0)" vector)
          ("(mapc #'identity data)" list)
          ("(coerce data 'vector)" list)
          ("(reverse data)" vector)
          ("(remove nil data)" vector)
          ("(funcall #'delete nil data)" list))
        for index from 0 do
    (let ((projection (if (member index '(1 5)) "car" "(lambda (x) (aref x 0))")))
      (sequence-shape-refuses
       (format nil "(let ((data (opaque-sequence)))
                      (if (typep data '~A)
                          (typep (funcall #'~A ~A) 'marker) nil))" shape projection expression)
       :external-result-class-observation)))
  (sequence-shape-refuses
   "(let ((data (opaque-sequence))) (if (typep data 'vector)
      (progn (fill data (make-instance 'marker)) 7) nil))"
   :external-shared-state-representation)
  (sequence-shape-refuses
   "(let ((data (opaque-sequence))) (if (typep data 'vector)
      (progn (setf (svref target 0) (aref data 0)) 7) nil))"
   :external-result-state :parameters "(target)" :domains '(vector))
  (sequence-shape-refuses
   "(let ((data (opaque-sequence))) (if (typep data 'vector) (fill data nil) nil))"
   :external-result-escape)
  ;; Receiver geometry supplies no native-data ABI for an unchanged import.
  (sequence-shape-refuses
   "(let ((data (opaque-sequence))) (if (typep data 'vector) (observe data) nil))"
   :external-value-representation)
  (dolist (callback '("#'(lambda (item) (typep item 'marker))" "#'probe"))
    (sequence-shape-refuses
     (format nil "(let ((data (opaque-sequence))) (if (typep data 'list)
                    (not (null (find t data :key ~A))) nil))" callback)
     :external-result-class-observation
     :helpers "(defun probe (item) (typep item 'marker))")))

(defun sequence-shape-coverage-tests ()
  ;; A compiler-selected leaf is not an authored source operation.
  (sequence-shape-refuses "(sb-impl::list-reverse '(1 2))" :call-target)
  ;; No checked caller can lend geometry to unrelated possible callers.
  (dolist (argument '("unknown" "(opaque-sequence)" "17"))
    (sequence-shape-refuses
     (format nil "(let ((data (opaque-sequence))) (if (typep data 'vector)
                    (progn (fill-length data) (fill-length ~A)) nil))" argument)
     :fill-sequence-domain :parameters "(unknown)" :domains '(t)
     :helpers "(defun fill-length (data) (fill data nil) 7)"))
  (sequence-shape-refuses
   "(let ((data (opaque-sequence))) (if (typep data 'vector)
      (progn (setq data replacement) (fill data nil) 7) nil))"
   :fill-sequence-domain :parameters "(replacement)" :domains '(t))
  (sequence-shape-refuses "(progn (fill (slot-value owner 'data) nil) 7)"
                          :fill-sequence-domain :parameters "(owner)"
                          :domains '(snowgrave.sequence-shape.fixture::table) :boot t)
  (sequence-shape-refuses
   "(flet ((snowgrave.sequence-shape.shadow::typep (data type)
             (declare (ignore data type)) t))
      (let ((data (opaque-sequence)))
        (if (snowgrave.sequence-shape.shadow::typep data 'vector)
            (progn (fill data nil) 7) nil)))"
   :fill-sequence-domain))

(defun sequence-shape-tests ()
  (sequence-shape-positive-tests)
  (sequence-shape-origin-tests)
  (sequence-shape-coverage-tests))
