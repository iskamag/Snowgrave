(in-package #:snowgrave.tests)

(defun relational-state-uncertain () nil)
(defun relational-state-invoke (function class) (funcall function (make-instance class)))

(defun relational-state-case (tag definitions body &key generics unsafe fresh (expected '(t)))
  ;; Every fixture compares actual host method order, values and effects.
  ;; The same source body must serve all joined inputs; no caller variants.
  (declare (ignore generics))
  (constructor-state-case
   (list :relational-state tag) definitions body expected :protocol t :refusal unsafe
   :external-operations '(relational-state-uncertain relational-state-invoke)
   :unit-check (lambda (unit)
                 (initialization-phase-source-check unit)
                 (let ((source (with-output-to-string (stream) (snowgrave:write-unit-source unit stream))))
                   (check (not (search ":RELATIONAL-VALUE" source)))
                   (check (not (search "FORMAL-RECEIVER" source))))
                 (when (member tag '(:custom-cem-pending-literal :standard-method-pending-literal))
                   (let* ((flow (getf (snowgrave:unit-report unit) :ordinary-function-flow))
                          (row (find "VALUE" (getf flow :generic-returns) :test #'equal
                                     :key (lambda (row) (second (getf row :generic-key))))))
                     (check (equal '(eql :pending) (getf row :primary-return-domain)))
                     (check (equal '((eql :pending)) (getf row :returned-value-domains)))
                     (check (getf row :returned-value-count-complete-p))))
                 (when fresh (initialization-phase-fresh-test unit)))))

(defun relational-state-tests ()
  (relational-state-case :equal-repairs-unbind
   "((defclass node () ((data :initform 17)))
     (defun repair (x y) (slot-makunbound y 'data) (setf(slot-value x 'data)17) (slot-value y 'data))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (snowgrave.tests::constructor-state-event(eql(repair n n)17))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)")
  (relational-state-case :equal-and-distinct-calls
   "((defclass node () ((data :initform 17))) (defclass peer () ((data :initform 23)))
     (defun write-read (x y) (setf(slot-value x 'data)17) (slot-value y 'data))
     (defmethod initialize-instance :around ((n node) &rest args)
       (declare(ignore args)) (let((other(make-instance 'peer))) (call-next-method)
         (snowgrave.tests::constructor-state-event(eql(write-read n n)17))
         (snowgrave.tests::constructor-state-event(eql(write-read n other)23)))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)")
  (relational-state-case :distinct-unbind-not-repaired
   "((defclass node () ((data :initform 17))) (defclass peer () ((data :initform 23)))
     (defun repair (x y) (slot-makunbound y 'data) (setf(slot-value x 'data)17) (slot-value y 'data))
     (defmethod initialize-instance :around ((n node) &rest args)
       (declare(ignore args)) (let((other(make-instance 'peer))) (call-next-method) (repair n other))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :unsafe t)
  (relational-state-case :may-alias-unbind-not-repaired
   "((defclass node () ((data :initform 17))) (defclass peer () ((data :initform 23)))
     (defun repair (x y) (slot-makunbound y 'data) (setf(slot-value x 'data)17) (slot-value y 'data))
     (defmethod initialize-instance :around ((n node) &rest args)
       (declare(ignore args)) (let((other(make-instance 'peer))) (call-next-method)
         (repair n (if(snowgrave.tests::relational-state-uncertain)n other)))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :unsafe t)
  (relational-state-case :self-field
   "((defclass node () ((data :initform 17) (link :type node)))
     (defun self-link (x) (setf(slot-value x 'link)x) (eq(slot-value x 'link)x))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (snowgrave.tests::constructor-state-event(self-link n))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)")
  (relational-state-case :cyclic-fields
   "((defclass node () ((data :initform 17) (link :initform nil)))
     (defclass peer () ((data :initform 23) (link :initform nil)))
     (defun connect (x y) (setf(slot-value x 'link)y (slot-value y 'link)x)
       (eq(slot-value(slot-value x 'link)'link)x))
     (defmethod initialize-instance :around ((n node) &rest args)
       (declare(ignore args)) (let((other(make-instance 'peer))) (call-next-method)
         (snowgrave.tests::constructor-state-event(connect n other)))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)")
  (relational-state-case :primary-identity-alias
   "((defclass node () ((data))) (defun alias (x) (values x :tag))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (let((saved(alias n))) (setf(slot-value saved 'data)17))
       (snowgrave.tests::constructor-state-event(eql(slot-value n 'data)17))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)")
  (relational-state-case :secondary-identity-alias
   "((defclass node () ((data))) (defun aliases (x) (values :tag x))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (multiple-value-bind(tag saved)(aliases n)
         (declare(ignore tag)) (setf(slot-value saved 'data)17))
       (snowgrave.tests::constructor-state-event(eql(slot-value n 'data)17))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)")
  (relational-state-case :secondary-other-identity
   "((defclass node () ((data :initform 17))) (defclass peer () ((data)))
     (defun aliases (x y) (declare(ignore x)) (values :tag y))
     (defmethod initialize-instance :around ((n node) &rest args)
       (declare(ignore args)) (let((other(make-instance 'peer))) (call-next-method)
         (multiple-value-bind(tag saved)(aliases n other)
           (declare(ignore tag)) (slot-value saved 'data)))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :unsafe t)
  (relational-state-case :prog1-old-value
   "((defclass node () ((data :initform 17)))
     (defun save (x) (prog1(slot-value x 'data)(setf(slot-value x 'data):changed)))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (snowgrave.tests::constructor-state-event(eql(save n)17))
       (snowgrave.tests::constructor-state-event(eq(slot-value n 'data):changed))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)")
  (relational-state-case :progn-new-value
   "((defclass node () ((data :initform 17)))
     (defun save (x) (progn(setf(slot-value x 'data):changed)(slot-value x 'data)))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (snowgrave.tests::constructor-state-event(eq(save n):changed))
       (snowgrave.tests::constructor-state-event(eq(slot-value n 'data):changed))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)")
  (relational-state-case :prog1-branch-value-point
   "((defclass node () ((data :initform 17) (y)))
     (defun save (x) (prog1(slot-value x 'data)(setf(slot-value x 'data):changed)))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (let((old(save n)))
         (unless(integerp old)(setf(slot-value n 'y)17))) (slot-value n 'y)))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :unsafe t)
  (relational-state-case :progn-branch-value-point
   "((defclass node () ((data :initform 17) (y)))
     (defun save (x) (progn(setf(slot-value x 'data):changed)(slot-value x 'data)))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (let((new(save n)))
         (when(integerp new)(setf(slot-value n 'y)17))) (slot-value n 'y)))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :unsafe t)
  (relational-state-case :reader-before-write
   "((defclass node () ((data :initform 17 :reader value)))
     (defmethod value :before ((n node)) (setf(slot-value n 'data)23))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (snowgrave.tests::constructor-state-event(eql(value n)23))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :generics '("value"))
  (relational-state-case :reader-after-write-old-result
   "((defclass node () ((data :initform 17 :reader value)))
     (defmethod value :after ((n node)) (setf(slot-value n 'data):changed))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (let((old(value n))) (snowgrave.tests::constructor-state-event(eql old 17)))
       (snowgrave.tests::constructor-state-event(eq(slot-value n 'data):changed))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :generics '("value"))
  (relational-state-case :reader-after-unbind-old-result
   "((defclass node () ((data :initform 17 :reader value)))
     (defmethod value :after ((n node)) (slot-makunbound n 'data))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (let((old(value n))) (snowgrave.tests::constructor-state-event(eql old 17)))
       (snowgrave.tests::constructor-state-event(slot-boundp n 'data))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :generics '("value"))
  (relational-state-case :reader-after-unbind-then-read
   "((defclass node () ((data :initform 17 :reader value)))
     (defmethod value :after ((n node)) (slot-makunbound n 'data))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (value n) (slot-value n 'data)))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :generics '("value") :unsafe t)
  (relational-state-case :reader-before-unbind
   "((defclass node () ((data :initform 17 :reader value)))
     (defmethod value :before ((n node)) (slot-makunbound n 'data))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (value n)))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :generics '("value") :unsafe t)
  (relational-state-case :reader-around-captures-old
   "((defclass node () ((data :initform 17 :reader value)))
     (defmethod value :after ((n node)) (setf(slot-value n 'data):changed))
     (defmethod value :around ((n node))
       (let((old(slot-value n 'data))) (call-next-method) (values old :around)))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (multiple-value-bind(old status)(value n)
         (snowgrave.tests::constructor-state-event(eql old 17))
         (snowgrave.tests::constructor-state-event(eq status :around)))
       (snowgrave.tests::constructor-state-event(eq(slot-value n 'data):changed))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :generics '("value"))
  (relational-state-case :reader-around-short-circuit
   "((defclass node () ((data :initform 17 :reader value)))
     (defmethod value :around ((n node)) (setf(slot-value n 'data):changed) (values 17 :skip))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (snowgrave.tests::constructor-state-event(eql(value n)17))
       (snowgrave.tests::constructor-state-event(eq(slot-value n 'data):changed))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :generics '("value"))
  (relational-state-case :helper-before-and-after-stock
   "((defclass node () ((data :initform 17))) (defun fetch(x)(slot-value x 'data))
     (defmethod initialize-instance :around ((n node) &rest args)
       (declare(ignore args)) (fetch n) (call-next-method))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (snowgrave.tests::constructor-state-event(eql(fetch n)17))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :unsafe t)
  (relational-state-case :helper-after-stock
   "((defclass node () ((data :initform 17))) (defun fetch(x)(slot-value x 'data))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (snowgrave.tests::constructor-state-event(eql(fetch n)17))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)")
  (relational-state-case :optional-default-supplied
   "((defclass node () ((data)))
     (defun supply(x &optional(flag(progn(setf(slot-value x 'data)17)nil)))
       (declare(ignore flag)) (slot-value x 'data))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (supply n t)))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :unsafe t)
  (relational-state-case :key-default-supplied
   "((defclass node () ((data)))
     (defun supply(x &key(flag(progn(setf(slot-value x 'data)17)nil)))
       (declare(ignore flag)) (slot-value x 'data))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (supply n :flag t)))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :unsafe t)
  (relational-state-case :aux-always-writes
   "((defclass node () ((data)))
     (defun supply(x &aux(flag(progn(setf(slot-value x 'data)17)nil)))
       (declare(ignore flag)) (slot-value x 'data))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (snowgrave.tests::constructor-state-event(eql(supply n)17))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)")
  (relational-state-case :optional-default-omitted
   "((defclass node () ((data)))
     (defun supply(x &optional(flag(progn(setf(slot-value x 'data)17)nil)))
       (declare(ignore flag)) (slot-value x 'data))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (snowgrave.tests::constructor-state-event(eql(supply n)17))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)")
  (relational-state-case :escaped-arbitrary-caller
   "((defclass node () ((data :initform 17))) (defclass peer () ((data :initform 29)))
     (defun fetch(x)(slot-value x 'data))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (fetch n)
       (snowgrave.tests::constructor-state-event
         (eql(snowgrave.tests::relational-state-invoke #'fetch 'peer)29))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :unsafe t)
  (relational-state-case :reader-after-write-value-point
   "((defclass node () ((data :initform 17 :reader value) (y)))
     (defmethod value :after ((n node)) (setf(slot-value n 'data):changed))
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args)) (let((old(value n)))
         (unless(integerp old)(setf(slot-value n 'y)17))) (slot-value n 'y)))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :generics '("value") :unsafe t)
  (relational-state-case :target-union-preserves-bound
   "((defclass node () ((data :initform 17)))
     (defun write-one(x)(setf(slot-value x 'data)23))
     (defun skip-one(x)(declare(ignore x))nil)
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args))
       (funcall(if(snowgrave.tests::relational-state-uncertain)#'write-one #'skip-one)n)
       (snowgrave.tests::constructor-state-event(integerp(slot-value n 'data)))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)")
  (relational-state-case :target-union-must-not-compose
   "((defclass node () ((data)))
     (defun write-one(x)(setf(slot-value x 'data)23))
     (defun skip-one(x)(declare(ignore x))nil)
     (defmethod initialize-instance :after ((n node) &rest args)
       (declare(ignore args))
       (funcall(if(snowgrave.tests::relational-state-uncertain)#'write-one #'skip-one)n)
       (slot-value n 'data)))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :unsafe t)
  (relational-state-case :union-substitution-preserves-bound
   "((defclass node () ((data :initform 17))) (defclass peer () ((data :initform 19)))
     (defun touch(target)(setf(slot-value target 'data)23)0)
     (defmethod initialize-instance :around ((n node) &rest args)
       (declare(ignore args)) (let((other(make-instance 'peer))) (call-next-method)
         (touch(if(snowgrave.tests::relational-state-uncertain)n other))
         (snowgrave.tests::constructor-state-event(eql(slot-value n 'data)17)))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)")
  (relational-state-case :union-substitution-must-not-bind
   "((defclass node () ((data :initform 17))) (defclass peer () ((data :initform 19)))
     (defun touch(target)(setf(slot-value target 'data)23)0)
     (defmethod initialize-instance :around ((n node) &rest args)
       (declare(ignore args)) (let((other(make-instance 'peer))) (call-next-method)
         (slot-makunbound n 'data)
         (touch(if(snowgrave.tests::relational-state-uncertain)n other))
         (slot-value n 'data))))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :unsafe t)
  (relational-state-case :captured-backing-loop
   "((defun scan (n)
        (dotimes (i 2) (snowgrave.tests::constructor-state-event(vectorp(slot-value n 'data)))) 17))"
   "(snowgrave.tests::constructor-state-event(eql(scan root)17)) t")
  (relational-state-case :captured-backing-flet
   "((defun scan (n)
        (flet ((fetch () (vectorp (slot-value n 'data)))) (fetch))))"
   "(snowgrave.tests::constructor-state-event(scan root)) t")
  (relational-state-case :family-backing-loop
   "((defclass node () ((data :initform (vector 17 23))))
      (defun scan (n)
        (dotimes (i 2) (snowgrave.tests::constructor-state-event(vectorp(slot-value n 'data)))) 17))"
   "(declare(ignore root)) (snowgrave.tests::constructor-state-event(eql(scan(make-instance 'node))17)) t")
  (relational-state-case :early-initializer-loop-no-family-fallback
   "((defclass node () ((data :initform (vector 17 23))))
      (defun scan (n)
        (dotimes (i 2) (snowgrave.tests::constructor-state-event(vectorp(slot-value n 'data)))) 17)
      (defmethod initialize-instance :around ((n node) &rest args)
        (declare(ignore args)) (scan n) (call-next-method)))"
   "(declare(ignore root)) (typep(make-instance 'node)'node)" :unsafe t)
  (relational-state-case :captured-clear-direct
   "((defgeneric clear (x))
      (defmethod clear ((x anchor)) (fill(slot-value x 'data)nil) 0))"
   "(clear root)" :expected '(0) :generics '("clear"))
  (relational-state-case :captured-clear-helper
   "((defgeneric clear (x)) (defun same (x) x)
      (defmethod clear ((x anchor)) (fill(slot-value x 'data)nil) 0))"
   "(clear(same root))" :expected '(0) :generics '("clear"))
  (relational-state-case :custom-cem-pending-literal
   "((define-method-combination literal-result () ((primary () :required t))
        (declare(ignore primary)) :pending)
      (defgeneric value (x) (:method-combination literal-result))
      (defmethod value ((x anchor)) (declare(ignore x)) :ignored))"
   "(eq(value root):pending)" :generics '("value"))
  (relational-state-case :standard-method-pending-literal
   "((defgeneric value (x))
      (defmethod value ((x anchor)) (declare(ignore x)) :pending))"
   "(eq(value root):pending)" :generics '("value"))
  (relational-state-case :class-qualified-disjoint-fields
    "((defclass left () ((data :initform (vector 17 23))))
       (defclass right () ((words :initform (vector 31))))
       (defgeneric measure (x))
       (defmethod measure ((x left)) (length (slot-value x 'data)))
       (defmethod measure ((x right)) (length (slot-value x 'words)))
       (defun read-owner (x) (measure x)))"
    "(declare (ignore root))
     (snowgrave.tests::constructor-state-event
       (and (= 2 (read-owner (make-instance 'left)))
            (= 1 (read-owner (make-instance 'right))))) t"
    :fresh t)
  ;; Two layouts enumerate their shared slot in different positions. A
  ;; keyed input join must stabilize without a semantic iteration cutoff.
  (relational-state-case :different-layout-slot-order
    "((defclass left () ((head :initform 1) (shared :initform 17)))
       (defclass right () ((shared :initform 23) (tail :initform 2)))
       (defun inspect-one (x) (integerp (slot-value x 'shared))))"
    "(declare (ignore root))
     (snowgrave.tests::constructor-state-event (inspect-one (make-instance 'left)))
     (snowgrave.tests::constructor-state-event (inspect-one (make-instance 'right))) 17"
    :expected '(17))
  (relational-state-case :recursive-read
    "((defclass node () ((data :initform 17)))
       (defun fetch (x remaining)
         (if (zerop remaining) (slot-value x 'data) (fetch x (1- remaining))))
       (defmethod initialize-instance :after ((n node) &rest args)
         (declare (ignore args)) (snowgrave.tests::constructor-state-event (eql (fetch n 2) 17))))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)")
  ;; No-base recursion is an admission-only refusal; never execute SPIN.
  (relational-state-case :recursive-no-base
    "((defun spin (x) (spin x)))" "(spin root)" :unsafe t)
  (relational-state-captured-reader-test)
  (relational-state-case :fresh-reader-helper
    "((defgeneric value (x)) (defclass node () ((data :initform 17 :reader value)))
       (defun fetch (x) (value x))
       (defmethod initialize-instance :after ((n node) &rest args)
         (declare (ignore args)) (snowgrave.tests::constructor-state-event (eql (fetch n) 17))))"
    "(declare (ignore root)) (typep (make-instance 'node) 'node)" :fresh t))

(defun relational-state-captured-reader-test ()
  ;; The original regression is fixed ROOT -> generated FACT -> ordinary
  ;; identity helper -> selected CLEAR -> native backing. No constructor or
  ;; method root is omitted to provide that captured state to the reader.
  (let* ((package (make-package (format nil "SNOWGRAVE.RELATIONAL.CAPTURE.~D"
                                      (incf *constructor-state-sequence*)) :use '("CL")))
         (forms (constructor-state-read
                 package
                 "((defclass table () ((data :initarg :data)))
                    (defclass holder () ((table :initarg :table :reader fact)))
                    (defun same (x) x)
                    (defgeneric clear (x))
                    (defmethod clear ((x table)) (length (fill (slot-value x 'data) nil)))
                    (defun entry (root)
                      (snowgrave.tests::constructor-state-event (eql (clear (same (fact root))) 2)) t))"))
         (table (intern "TABLE" package)) (holder (intern "HOLDER" package))
         (entry (intern "ENTRY" package)))
    (dolist (form forms) (eval form))
    (let* ((native (make-instance holder :table (make-instance table :data (vector 17 23))))
           (root (make-instance holder :table (make-instance table :data (vector 17 23))))
           (unit (snowgrave:close-source-unit
                  (list :forms forms) :unit-name (list :relational-captured-reader *constructor-state-sequence*)
                  :closed-classes (list table holder)
                  :closed-generics (mapcar (lambda (name) (intern name package)) '("FACT" "CLEAR"))
                  :universe (list table holder 'vector t) :entries (list entry)
                  :external-domains (list (list entry (list (list 'eql root))))
                  :external-operations '(constructor-state-event))))
      (check (equal (constructor-state-observation (lambda () (funcall entry native)) nil)
                    (constructor-state-observation (snowgrave:unit-function unit entry :bind-configuration t) nil)))
      (initialization-phase-source-check unit)
      (let* ((source (with-output-to-string (stream) (snowgrave:write-unit-source unit stream)))
             (key (snowgrave::function-name-key (intern "SAME" package)))
             (definitions (loop for form in (snowgrave:unit-source unit)
                                when (and (consp form) (eq (first form) 'defun)) collect (second form))))
        (check (= 1 (count-if (lambda (name)
                               (and (symbolp name)
                                    (equal key (ignore-errors (read-from-string (symbol-name name))))))
                             definitions)))
        (check (not (search ":RELATIONAL-VALUE" source)))
        (check (not (search "FORMAL-RECEIVER" source))))
      (initialization-phase-fresh-test unit))))
