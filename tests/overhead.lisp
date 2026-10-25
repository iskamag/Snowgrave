(in-package #:snowgrave.tests)

(defun bounded-call-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :bounded-calls
       "((defgeneric operation (n &optional a b))
          (defmethod operation :around ((n number) &optional (a :around ap) (b :around-b bp))
            (snowgrave.tests::note-event (list :enter n a (not (null ap)) b (not (null bp))))
            (unwind-protect (call-next-method) (snowgrave.tests::note-event :exit)))
          (defmethod operation :before ((n number) &optional (a :before ap) (b :before-b bp))
            (snowgrave.tests::note-event (list :before n a (not (null ap)) b (not (null bp)))))
          (defmethod operation :after ((n number) &optional (a :after ap) (b :after-b bp))
            (snowgrave.tests::note-event (list :after n a (not (null ap)) b (not (null bp)))))
          (defmethod operation ((n number) &optional (a :base ap) (b :base-b bp))
            (snowgrave.tests::note-event :base)
            (values (list n a (not (null ap)) b (not (null bp))) :secondary))
          (defmethod operation ((n integer) &optional (a :child ap) (b :child-b bp))
            (snowgrave.tests::note-event (list :child n a (not (null ap)) b (not (null bp))))
            (setq n \"mutated\" a :changed b :changed)
            (values (multiple-value-list (call-next-method))
                    (multiple-value-list (call-next-method))))
          (defun entry (arguments)
            (handler-case (apply #'operation arguments)
              (error (condition) (not (null (typep condition 'error))))))
          (defun direct () (operation 7))
          (defgeneric add (n &optional amount))
          (defmethod add ((n number) &optional (amount 2)) (+ n amount))
          (defmethod add ((n integer) &optional (amount (call-next-method)))
            (declare (ignore amount)) (call-next-method))
          (defun omitted (n) (add n))
          (defun supplied (n) (add n 3)))"
       "(entry direct omitted supplied)" "((entry (list)) (direct ()) (omitted (integer)) (supplied (integer)))"
       "(operation add)" :universe "(number integer)" :external '(note-event))
    ;; Defaults belong to each method. SETQ of method parameters must not
    ;; change either next invocation, including its optional supplied prefix.
    (dolist (arguments '((7) (7 nil) (7 nil :given) (1/2) ("miss")
                        (7 1 2 3) ("miss" 1 2 3)))
      (compare-entry unit package "ENTRY" (list arguments)))
    (compare-entry unit package "OMITTED" '(7) '((9) nil) :native-p #-ccl t #+ccl nil)
    (compare-entry unit package "SUPPLIED" '(7) '((10) nil))
    (let ((name (find-symbol "DIRECT" package)))
      (check (equal (observed-call (fdefinition name) nil)
                    (observed-call (snowgrave:bind-entry unit name nil) nil))
             "Configured qualifier/default/next-method semantics differ"))
    (let ((name (find-symbol "OMITTED" package)))
      (check (= 9 (funcall (snowgrave:bind-entry unit name '(7))))
             "Configured next-method call inside an optional default differs"))
    (dolist (name '("OMITTED" "SUPPLIED"))
      (check-zero-call-allocation
       (snowgrave:unit-function unit (find-symbol name package)) 7 name))))

(defun call-loop (function argument count)
  ;; Kept outside the generated program; do not let a compiler discard or
  ;; fold the measured call. The allocating calibration checks the counter.
  (let ((result nil))
    (dotimes (i count result) (setf result (funcall function argument)))))

(defun check-zero-call-allocation (function argument description)
  ;; SBCL charges a one-time cost to the first window after a full GC, even for
  ;; #'IDENTITY, so that window is discarded. A genuinely allocating callee
  ;; allocates in every window, which the remaining ones still catch.
  (unless (test-bytes-consed) (return-from check-zero-call-allocation))
  (labels ((window ()
             (let ((before (test-bytes-consed)))
               (call-loop function argument 100000)
               (- (test-bytes-consed) before))))
    (test-gc)
    (call-loop function argument 1000)
    (window)
    (dotimes (i 3)
      (let ((bytes (window)))
        (check (zerop bytes) "~A allocates ~D bytes during warmed bounded calls" description bytes)))))

(defun slot-helper-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :slot-helpers
       "((defclass base () ((x :type integer :accessor x)))
          (defclass prefix () ((padding :initform :padding)))
          (defclass child (prefix base) ())
          (defclass unrelated () ((x :type symbol :initform :symbol :accessor x)))
          (defun read-restart (store)
            (let ((object (make-instance 'child)))
              (values
               (handler-bind ((unbound-slot
                               (lambda (condition)
                                 (declare (ignore condition))
                                 (invoke-restart (if store 'store-value 'use-value) 17))))
                 (slot-value object 'x))
               (slot-boundp object 'x))))
          (defun reject-store ()
            (let ((object (make-instance 'child)))
              (values
               (handler-case
                   (handler-bind ((unbound-slot
                                   (lambda (condition)
                                     (declare (ignore condition))
                                     (invoke-restart 'store-value :wrong))))
                     (x object))
                 (type-error () :rejected))
               (slot-boundp object 'x))))
          (defun use-untyped ()
            (let ((object (make-instance 'base)))
              (handler-bind ((unbound-slot
                              (lambda (condition)
                                (declare (ignore condition))
                                (invoke-restart 'use-value :not-stored))))
                (x object))))
          (defun missing (name)
            (handler-case (slot-boundp (make-instance 'base) name)
              (error (condition) (not (null (typep condition 'error))))))
          (defun fields ()
            (let ((a (make-instance 'child)) (b (make-instance 'unrelated)))
              (setf (x a) 31 (x b) nil)
              (values (x a) (x b) (slot-boundp b 'x)
                      (eq a (slot-makunbound a 'x)) (slot-boundp a 'x))))
          (defparameter *cell* (make-instance 'child))
          (defun access (n) (setf (x *cell*) n) (x *cell*)))"
       "(read-restart reject-store use-untyped missing fields access)"
       "((read-restart (t)) (reject-store ()) (use-untyped ()) (missing (symbol)) (fields ()) (access (integer)))"
       "(x (setf x))")
    (compare-entry unit package "READ-RESTART" '(nil) '((17 nil) nil) :native-p #-ecl t #+ecl nil)
    ;; STORE-VALUE is Snowgrave's explicit restart contract; native CCL and ECL do
    ;; not provide it for SLOT-UNBOUND. ECL also lacks USE-VALUE.
    (compare-entry unit package "READ-RESTART" '(t) '((17 t) nil) :native-p #-(or ccl ecl) t #+(or ccl ecl) nil)
    ;; Writing outside a declared CLOS slot type has undefined consequences.
    ;; Check Snowgrave's checked-write contract without using that as a native
    ;; differential oracle (SBCL's STORE-VALUE need not enforce the type).
    (check (equal '((:rejected nil) nil)
                  (observed-call (snowgrave:unit-function unit (find-symbol "REJECT-STORE" package)) nil))
           "Failed restart store changed boundness")
    (compare-entry unit package "USE-UNTYPED" nil '((:not-stored) nil) :native-p #-ecl t #+ecl nil)
    (compare-entry unit package "FIELDS" nil '((31 nil t t nil) nil))
    ;; Equal print names do not make slot symbols interchangeable.
    (dolist (name (list :x (make-symbol "X") :missing))
      (compare-entry unit package "MISSING" (list name)))
    (check-zero-call-allocation
     (snowgrave:unit-function unit (find-symbol "ACCESS" package)) 7 "reader and writer"))
  (when (test-bytes-consed)
   (let ((before (test-bytes-consed)))
    (call-loop (lambda (n) (list n)) 7 100000)
    (check (> (- (test-bytes-consed) before) 1000000)
           "Allocation calibration failed"))))

(defun literal-scale-tests ()
  ;; A large literal graph is data, not thousands of branches in one compiled
  ;; initializer. Include distinct equal strings and both cons/vector cycles.
  (let* ((number (incf *fixture-sequence*))
         (package (make-package (format nil "SNOWGRAVE.CORE.FIXTURE.~D" number) :use '("COMMON-LISP")))
         (entry (intern "ENTRY" package))
         (graph (make-array 6000))
         (cycle (cons :cycle nil)))
    (setf (cdr cycle) cycle)
    (dotimes (i (length graph)) (setf (aref graph i) (list i (copy-seq "equal"))))
    (setf (aref graph 0) graph (aref graph 1) cycle)
    (let* ((unit (snowgrave:close-source-unit
                  (list :forms `((defun ,entry () ',graph)))
                  :unit-name (list :literal-scale number)
                  :entries (list entry) :external-domains (list (list entry nil))))
           (result (funcall (snowgrave:unit-function unit entry))))
      (check (and (eq result (aref result 0))
                  (eq (aref result 1) (cdr (aref result 1))))
             "Literal reconstruction lost a cycle")
      (check (= 5999 (first (aref result 5999))) "Literal reconstruction lost the final node")
      (check (and (equal (second (aref result 2)) (second (aref result 3)))
                  (not (eq (second (aref result 2)) (second (aref result 3)))))
             "Literal reconstruction coalesced distinct strings"))))
