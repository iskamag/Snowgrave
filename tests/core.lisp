(defpackage #:snowgrave.tests
  (:use #:common-lisp)
  (:export #:run-tests))

(in-package #:snowgrave.tests)

(defvar *checks* 0)
(defvar *fixture-sequence* 0)
(defvar *events* nil)
(defvar *macro-expansion-count* 0)

(defmacro snapshot-token ()
  (incf *macro-expansion-count*))

(defun note-event (event)
  (push event *events*)
  event)

(defun external-operation (value)
  (+ value 100))

(defun switch-external-operation (value)
  (setf (fdefinition 'external-operation) (lambda (argument) (+ argument 200)))
  value)

(defun check (truth description &rest arguments)
  (incf *checks*)
  (unless truth
    (error "Snowgrave check failed: ~?" description arguments)))

(defun fixture-read (package text)
  (let ((*package* package) (*read-eval* nil))
    (read-from-string text)))

(defun make-fixture (tag source entries domains generics &key (universe "()") external)
  "Load the original CLOS program and close exactly those owned source forms."
  (let* ((number (incf *fixture-sequence*))
         (package (make-package (format nil "SNOWGRAVE.CORE.FIXTURE.~D" number) :use '("COMMON-LISP")))
         (forms (fixture-read package source))
         (classes (loop for form in forms when (eq (first form) 'defclass) collect (second form))))
    (mapc #'eval forms)
    (values
     (snowgrave:close-source-unit
      (list :forms forms) :unit-name (list :core tag number)
      :closed-classes classes
      :universe (remove-duplicates (append classes (fixture-read package universe)))
      :closed-generics (fixture-read package generics)
      :entries (fixture-read package entries)
      :external-domains (fixture-read package domains)
      :external-operations external)
     package)))

(defun observed-call (function arguments)
  (let ((*events* nil))
    (let ((results (multiple-value-list (apply function arguments))))
      (list results (reverse *events*)))))

(defun compare-entry (unit package name arguments &optional expected)
  (let* ((symbol (find-symbol name package))
         (open (observed-call (fdefinition symbol) arguments))
         (closed (observed-call (snowgrave:unit-function unit symbol) arguments)))
    (when expected
      (check (equal open expected) "~A open observation: ~S, expected ~S" name open expected))
    (check (equal open closed) "~A differs: open ~S, closed ~S" name open closed)
    closed))

(defun method-linkage-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :method-links
       "((defclass base () ((value :initarg :value :accessor value)))
          (defclass child (base) ())
          (defgeneric finish (object delta))
          (defmethod finish ((object base) delta)
            (snowgrave.tests::note-event :finish)
            (values (+ (value object) delta) :finished))
          (defun relay (object delta) (finish object delta))
          (defgeneric start (object delta))
          (defmethod start :around ((object base) delta)
            (snowgrave.tests::note-event :around-enter)
            (unwind-protect (call-next-method)
              (snowgrave.tests::note-event :around-exit)))
          (defmethod start :before ((object base) delta)
            (snowgrave.tests::note-event :before))
          (defmethod start :after ((object base) delta)
            (snowgrave.tests::note-event :after))
          (defmethod start ((object base) delta)
            (snowgrave.tests::note-event :base)
            (relay object delta))
          (defmethod start ((object child) delta)
            (snowgrave.tests::note-event (if (next-method-p) :child-next :missing-next))
            (call-next-method))
          (defun entry (n) (start (make-instance 'child :value n) 7))
          (defun indirect (n)
            (let ((function #'start))
              (funcall function (make-instance 'child :value n) 7)))
          (defun spread (n) (apply #'start (list (make-instance 'child :value n) 7)))
          (defun map-relay (object) (start object 7))
          (defun mapped (n)
            (flet ((map-relay (object) (declare (ignore object)) :wrong-local))
              (mapcar 'map-relay (list (make-instance 'child :value n)))))
          (defun keyed (n)
            (let ((target (make-instance 'child :value n)))
              (eq target (find n (list (make-instance 'child :value (+ n 1)) target) :key 'value)))))"
       "(entry indirect spread mapped keyed)"
       "((entry (number)) (indirect (number)) (spread (number)) (mapped (number)) (keyed (number)))"
       "(value (setf value) finish start)" :universe "(base child number)"
       :external '(note-event))
    (let ((expected '((12 :finished) (:around-enter :before :child-next :base :finish :after :around-exit)))
          (mapped-expected '(((12)) (:around-enter :before :child-next :base :finish :after :around-exit))))
      (dolist (name '("ENTRY" "INDIRECT" "SPREAD"))
        (compare-entry unit package name '(5) expected))
      (compare-entry unit package "MAPPED" '(5) mapped-expected)
      (compare-entry unit package "KEYED" '(5) '((t) nil))
      ;; Poison both generic leaves and the intervening original helper.
      ;; A hidden open call now fails instead of accidentally matching output.
      (dolist (name '("START" "FINISH" "VALUE"))
        (sb-mop:set-funcallable-instance-function
         (fdefinition (find-symbol name package))
         (lambda (&rest arguments) (declare (ignore arguments)) (error "Original generic reached."))))
      (dolist (name '("RELAY" "MAP-RELAY"))
        (setf (fdefinition (find-symbol name package))
              (lambda (&rest arguments) (declare (ignore arguments)) (error "Original helper reached."))))
      (dolist (name '("ENTRY" "INDIRECT" "SPREAD"))
        (check (equal expected (observed-call (snowgrave:unit-function unit (find-symbol name package)) '(5)))
               "~A retained an original binding" name))
      (check (equal mapped-expected
                    (observed-call (snowgrave:unit-function unit (find-symbol "MAPPED" package)) '(5)))
             "Quoted MAPCAR callback retained its original helper")
      (check (equal '((t) nil)
                    (observed-call (snowgrave:unit-function unit (find-symbol "KEYED" package)) '(5)))
             "Quoted FIND key retained its original reader"))))

(defun record-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :records
       "((defclass left () ((x :initarg :x :initform 3 :accessor x)))
          (defclass right () ((y :initform (list 5) :accessor y)))
          (defclass both (left right) ((empty)))
          (defun entry (n)
            (let ((a (make-instance 'both :x n)) (b (make-instance 'both)))
              (let ((initial (list (x a) (x b) (y a)
                                   (typep a 'left) (typep a 'right)
                                   (eq (y a) (y b)) (slot-boundp a 'empty))))
                (setf (x a) (+ n 1) (slot-value a 'empty) 9)
                (let ((written (list (x a) (slot-value a 'empty) (slot-boundp a 'empty))))
                  (slot-makunbound a 'empty)
                  (values initial written (slot-boundp a 'empty)
                          (handler-case (slot-value a 'empty)
                            (unbound-slot (condition)
                              (and (eq a (unbound-slot-instance condition))
                                   (eq 'empty (cell-error-name condition))))))))))
          (defun construct () (make-instance 'both)))"
       "(entry construct)" "((entry (number)) (construct ()))"
       "(x (setf x) y (setf y))" :universe "(left right both number)")
    (compare-entry unit package "ENTRY" '(10)
                   '(((10 3 (5) t t nil nil) (11 9 t) nil t) nil))
    (let* ((constructor (snowgrave:unit-function unit (find-symbol "CONSTRUCT" package)))
           (first (funcall constructor)) (second (funcall constructor)))
      (check (and (typep first 'structure-object) (not (typep first 'standard-object)))
             "Closed construction did not produce an ordinary structure")
      (check (not (eq first second)) "Construction reused an instance"))
    (check (>= (count 'defstruct (snowgrave:unit-source unit) :key #'first) 3)
           "Emitted source does not contain the three class structures")))

(defun dynamic-record-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :dynamic-records
       "((defun mark (label value) (snowgrave.tests::note-event label) value)
          (defclass alpha ()
            ((x :initarg :x :initform 7) (fresh :initform (list 5)))
            (:default-initargs :x (mark :default-x 11)))
          (defclass beta () ((y :initarg :y :initform 8)))
          (defparameter *cold* (make-instance (identity 'alpha) :x 91))
          (defun cold () (slot-value *cold* 'x))
          (defun indirect ()
            (let ((class 'alpha) (constructor #'make-instance))
              (values (slot-value (funcall constructor class :x 27) 'x)
                      (slot-value (make-instance (find-class class) :x 33) 'x))))
          (defun construct ()
            (let ((a (make-instance (mark :class 'alpha)
                                   (mark :key-1 :x) (mark :value-1 nil)
                                   (mark :key-2 :x) (mark :value-2 23)))
                  (b (make-instance (identity 'alpha) :unknown 2 :allow-other-keys t)))
              (values (slot-value a 'x) (slot-value b 'x)
                      (eq (slot-value a 'fresh) (slot-value b 'fresh)))))
          (defun reject-class ()
            (handler-case
                (make-instance (mark :class 'beta) (mark :key :x) (mark :value 2))
              (program-error () :program-error)))
          (defun reject-default ()
            (handler-case
                (make-instance (mark :class 'alpha) (mark :key :unknown) (mark :value 2))
              (program-error () :program-error)))
          (defun bad-condition ()
            (handler-case (make-instance 'alpha :unknown 2)
              (program-error (condition) condition)))
          (defun dynamic-slots ()
            (let ((object (make-instance (identity 'beta))) (name 'y))
              (setf (slot-value (mark :object object) (mark :slot name)) (mark :new 19))
              (let ((before (list (slot-value object name) (slot-boundp object name))))
                (slot-makunbound object name)
                (values before (slot-boundp object name))))))"
       "(cold indirect construct reject-class reject-default bad-condition dynamic-slots)"
       "((cold ()) (indirect ()) (construct ()) (reject-class ()) (reject-default ()) (bad-condition ()) (dynamic-slots ()))"
       "()" :external '(note-event))
    (compare-entry unit package "COLD" nil '((91) nil))
    (compare-entry unit package "INDIRECT" nil '((27 33) nil))
    (compare-entry unit package "CONSTRUCT" nil
                   '((nil 11 nil) (:class :key-1 :value-1 :key-2 :value-2 :default-x)))
    (compare-entry unit package "REJECT-CLASS" nil '((:program-error) (:class :key :value)))
    (compare-entry unit package "REJECT-DEFAULT" nil
                   '((:program-error) (:class :key :value :default-x)))
    (compare-entry unit package "DYNAMIC-SLOTS" nil '(((19 t) nil) (:object :slot :new)))
    (let* ((entry (find-symbol "BAD-CONDITION" package))
           (original (funcall entry))
           (closed (funcall (snowgrave:unit-function unit entry))))
      (check (string= (princ-to-string original) (princ-to-string closed))
             "Closed initarg condition exposes its physical class descriptor: ~A" closed))
    (let* ((source (snowgrave:unit-source unit))
           (definition (find-if (lambda (form)
                                  (and (eq (first form) 'defun) (symbolp (second form))
                                       (string= (symbol-name (second form)) "MAKE-INSTANCE")))
                                source))
           (name (second definition))
           (direct nil) (captured nil) (original nil))
      (labels ((visit (form)
                 (when (consp form)
                   (when (eq (first form) name) (setf direct t))
                   (when (equal form (list 'function name)) (setf captured t))
                   (when (or (eq (first form) 'make-instance)
                             (equal form '(function make-instance)))
                     (setf original t))
                   (visit (car form)) (visit (cdr form)))))
        (visit source))
      (check (and name (not (eq name 'make-instance))
                  (not (eq (symbol-package name) (find-package :cl)))
                  direct captured (not original))
             "Construction did not consistently use the output package's MAKE-INSTANCE binding"))))

(defun argument-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :arguments
       "((defclass cell () ((value :initarg :value :reader value)))
          (defgeneric combine (object &optional amount &rest rest &key offset))
          (defmethod combine ((object cell) &optional (amount 3 suppliedp) &rest rest &key (offset 5))
            (values (+ (value object) (or amount 0) offset) suppliedp rest))
          (defun omitted (n) (combine (make-instance 'cell :value n)))
          (defun supplied-nil (n) (combine (make-instance 'cell :value n) nil :offset 7))
          (defun keyword-entry (n) (combine (make-instance 'cell :value n) 8 :offset 9))
          (defun indirect (n)
            (apply #'combine (list (make-instance 'cell :value n) 8 :offset 9)))
          (defgeneric calculate (n &optional value))
          (defmethod calculate ((n number) &optional (value 3)) (+ n value))
          (defmethod calculate ((n integer) &optional (value (call-next-method))) (* 2 value))
          (defun default-next (n) (calculate n)))"
       "(omitted supplied-nil keyword-entry indirect default-next)"
       "((omitted (number)) (supplied-nil (number)) (keyword-entry (number)) (indirect (number)) (default-next (integer)))"
       "(value combine calculate)" :universe "(cell integer number)")
    (compare-entry unit package "OMITTED" '(5) '((13 nil nil) nil))
    (compare-entry unit package "SUPPLIED-NIL" '(5) '((12 t (:offset 7)) nil))
    (compare-entry unit package "KEYWORD-ENTRY" '(5) '((22 t (:offset 9)) nil))
    (compare-entry unit package "INDIRECT" '(5) '((22 t (:offset 9)) nil))
    (compare-entry unit package "DEFAULT-NEXT" '(5) '((16) nil))))

(defun control-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :control
       "((defclass cell () ((value :initarg :value :reader value)))
          (defgeneric leave (object))
          (defmethod leave :around ((object cell))
            (snowgrave.tests::note-event :enter)
            (unwind-protect (call-next-method) (snowgrave.tests::note-event :cleanup)))
          (defmethod leave :after ((object cell)) (snowgrave.tests::note-event :after))
          (defmethod leave ((object cell)) (throw 'done (values (value object) :escape)))
          (defun entry (n) (catch 'done (leave (make-instance 'cell :value n)))))"
       "(entry)" "((entry (number)))" "(value leave)" :universe "(cell number)"
       :external '(note-event))
    (compare-entry unit package "ENTRY" '(17) '((17 :escape) (:enter :cleanup)))))

(defun binding-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :bindings
       "((defgeneric operation (x))
          (defmethod operation ((x number)) (+ x 100))
          (defun helper (x) (operation x))
          (defun entry (n)
            (let ((operation 3) (helper 4))
              (flet ((operation (x) (+ x 1)) (helper (x) (+ x 2)))
                (values operation helper (operation n) (funcall #'helper n)))))
          (defparameter *offset* 10)
          (defun read-offset () *offset*)
          (defun keyword-offset (&key (*offset* 3)) (read-offset))
          (defun dynamic-entry (n)
            (values (read-offset)
                    (let ((*offset* n)) (read-offset))
                    (read-offset) (keyword-offset :*offset* n) (read-offset)))
          (defun external-callback (n)
            (flet ((snowgrave.tests::external-operation (x) (+ x 1)))
              (values (funcall 'snowgrave.tests::external-operation n)
                      (mapcar 'snowgrave.tests::external-operation (list n))
                      (funcall #'snowgrave.tests::external-operation n))))
          (defun external-timing (n)
            (funcall 'snowgrave.tests::external-operation
                     (snowgrave.tests::switch-external-operation n))))"
       "(entry dynamic-entry external-callback external-timing)"
       "((entry (number)) (dynamic-entry (number)) (external-callback (number)) (external-timing (number)))"
       "(operation)" :universe "(number)"
       :external '(external-operation switch-external-operation))
    (compare-entry unit package "ENTRY" '(7) '((3 4 8 9) nil))
    (compare-entry unit package "DYNAMIC-ENTRY" '(27) '((10 27 10 27 10) nil))
    (compare-entry unit package "EXTERNAL-CALLBACK" '(7) '((107 (107) 8) nil))
    ;; A quoted symbol resolves its global function after argument evaluation.
    ;; Reset before each call so the open run cannot prepare the closed run.
    (let ((original (fdefinition 'external-operation))
          (name (find-symbol "EXTERNAL-TIMING" package)))
      (unwind-protect
           (let ((open (observed-call (fdefinition name) '(7))))
             (check (equal open '((207) nil)) "Open symbol-designator lookup happened too early")
             (setf (fdefinition 'external-operation) original)
             (check (equal open (observed-call (snowgrave:unit-function unit name) '(7)))
                    "Closing changed global symbol-designator lookup timing"))
        (setf (fdefinition 'external-operation) original)))))

(defun native-partition-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :native-partition
       "((defgeneric classify (x))
          (defmethod classify ((x integer)) (declare (ignore x)) :integer)
          (defmethod classify ((x number)) (declare (ignore x)) :number)
          (defmethod classify ((x symbol)) (declare (ignore x)) :symbol)
          (defmethod classify ((x t)) (declare (ignore x)) :other)
          (defun entry (x) (classify x)))"
       "(entry)" "((entry (t)))" "(classify)" :universe "(integer number symbol)")
    (loop for value in '(3 1/2 :hello "text" (1 2))
          for result in '(:integer :number :symbol :other :other)
          do (compare-entry unit package "ENTRY" (list value) (list (list result) nil)))))

(defun method-boundary-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :method-boundaries
       "((defgeneric only-integer (x))
          (defmethod only-integer ((x integer)) (call-next-method))
          (defgeneric greeting (x))
          (defmethod greeting ((x integer)) \"hello\")
          (defun missing ()
            (handler-case (only-integer \"outside\")
              (error (condition) (values (type-of condition) t))))
          (defun no-next ()
            (handler-case (only-integer 3)
              (error (condition) (values (type-of condition) t))))
          (defun text-result () (greeting 3)))"
       "(missing no-next text-result)" "((missing ()) (no-next ()) (text-result ()))"
       "(only-integer greeting)" :universe "(integer)")
    (dolist (name '("MISSING" "NO-NEXT"))
      (let ((observation (compare-entry unit package name nil)))
        (check (second (first observation)) "~A did not take its condition path" name)))
    (compare-entry unit package "TEXT-RESULT" nil '(("hello") nil))))

(defun constant-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :constant-order
       "((defconstant +base+ 17)
          (defun make-offset () (+ +base+ 15))
          (defconstant +offset+ (make-offset))
          (defun entry () (+ +base+ +offset+)))"
       "(entry)" "((entry ()))" "()")
    (compare-entry unit package "ENTRY" nil '((49) nil)))
  (multiple-value-bind (unit package)
      (make-fixture
       :constant-generated-code
       "((defconstant +base+ 17)
          (defclass cell () ((value :initform +base+ :reader value)))
          (defgeneric total (object))
          (defmethod total ((object cell)) (+ +base+ (value object)))
          (defun entry () (total (make-instance 'cell))))"
       "(entry)" "((entry ()))" "(value total)")
    (compare-entry unit package "ENTRY" nil '((34) nil)))
  ;; The builder installs this constant before closed rewriting refuses the
  ;; EVAL call. Cleanup must preserve the original condition.
  (let ((feature nil))
    (handler-case
        (make-fixture
         :constant-cleanup
         "((defconstant +base+ 17)
            (defun entry () (eval '+base+)))"
         "(entry)" "((entry ()))" "()")
      (snowgrave:snowgrave-error (condition)
        (setf feature (snowgrave:error-feature condition))))
    (check (eq :open-operation feature)
           "Constant cleanup lost the original EVAL refusal: ~S" feature)))

(defun logical-equalp-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :logical-equalp
       "((defclass cell () ((value :initform 7)))
          (defun entry ()
            (let ((a (make-instance 'cell)) (b (make-instance 'cell)))
              (values (equalp a b) (equalp a a)
                      (equalp (list a) (list b))
                      (equalp (vector (list a)) (vector (list b)))
                      (funcall #'equalp a b)
                      (equalp \"AbC\" \"aBc\") (equalp 3 3.0)
                      (equalp #(1 #\\A (2)) #(1.0 #\\a (2.0)))))))"
       "(entry)" "((entry ()))" "()")
    (compare-entry unit package "ENTRY" nil '((nil t nil nil nil t t t) nil))))

(defun logical-metadata-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :logical-metadata
       "((defclass base () ((x :initform 7)))
          (defclass child (base) ())
          (defun admitted-p (object name)
            (let ((class (class-of object)))
              (and (eq (class-of class) (find-class 'standard-class))
                   (progn (sb-mop:finalize-inheritance class) t)
                   (let ((slot (find name (sb-mop:class-slots class)
                                     :key #'sb-mop:slot-definition-name)))
                     (and slot
                          (eq (class-of slot) (find-class 'sb-mop:standard-effective-slot-definition))
                          (eq (sb-mop:slot-definition-allocation slot) :instance)
                          (eq (sb-mop:slot-definition-type slot) t)
                          (slot-boundp object name))))))
          (defun entry ()
            (let ((object (make-instance 'child)))
              (values (slot-value object 'x) (admitted-p object 'x)
                      (eq (class-of object) (find-class 'child))
                      (eq (class-of object) (find-class 'base))
                      (class-name (class-of object))))))"
       "(entry)" "((entry ()))" "()")
    (compare-entry unit package "ENTRY" nil
                   (list (list 7 t t nil (find-symbol "CHILD" package)) nil))))

(defun frozen-macro-tests ()
  ;; Do not evaluate an independent open fixture first: that would expand the
  ;; stateful macro against different build inputs than the snapshot under test.
  (let* ((number (incf *fixture-sequence*))
         (package (make-package (format nil "SNOWGRAVE.CORE.FIXTURE.~D" number) :use '("COMMON-LISP")))
         (forms (fixture-read package
                 "((defgeneric version ())
                    (defmethod version ()
                      (return-from version (values (snowgrave.tests::snapshot-token) :snapshot)))
                    (defun entry () (return-from entry (version))))"))
         (*macro-expansion-count* 0)
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name (list :core :frozen-macro number)
                :closed-classes nil :closed-generics (fixture-read package "(version)")
                :universe nil :entries (fixture-read package "(entry)")
                :external-domains (fixture-read package "((entry ()))")))
         (entry (snowgrave:unit-function unit (find-symbol "ENTRY" package))))
    (check (= 1 *macro-expansion-count*) "Owned macro expanded ~D times while closing" *macro-expansion-count*)
    (check (equal '(1 :snapshot) (multiple-value-list (funcall entry)))
           "Zero-argument effective method did not retain the frozen expansion")
    (check (equal '(1 :snapshot) (multiple-value-list (funcall entry)))
           "Repeated call changed the frozen expansion")
    (check (= 1 *macro-expansion-count*) "Runtime call expanded source again")))

(defun fresh-artifact-test ()
  (multiple-value-bind (unit package)
      (make-fixture
       :artifact
       "((defclass cell () ((value :initarg :value :reader value)))
          (defgeneric next-value (object))
          (defmethod next-value ((object cell)) (+ 1 (value object)))
          (defun helper (object) (next-value object))
          (defun entry (n) (helper (make-instance 'cell :value n)))
          (defun literals ()
            (values (eq '#1=(1 2) '#1#) (eq '#1# '(1 2))
                    (eq #2=\"same\" '#2#) (eq #2# \"same\")
                    (eq #3=#(1 2) '#3#) (eq #3# #(1 2)))))"
       "(entry literals)" "((entry (number)) (literals ()))"
       "(value next-value)" :universe "(cell number)")
    (compare-entry unit package "ENTRY" '(41) '((42) nil))
    (compare-entry unit package "LITERALS" nil '((t nil t nil t nil) nil))
    (let* ((metadata (snowgrave:unit-metadata unit))
           (entry (find (find-symbol "ENTRY" package) (getf metadata :entries)
                        :key (lambda (row) (getf row :name))))
           (key (getf entry :code-key))
           (literal-key (getf (find (find-symbol "LITERALS" package) (getf metadata :entries)
                                   :key (lambda (row) (getf row :name))) :code-key))
           (directory (merge-pathnames
                       (format nil "snowgrave-core-artifact-~D-~D/" (get-universal-time) *fixture-sequence*)
                       (uiop:temporary-directory)))
           (source (merge-pathnames "unit.lisp" directory))
           (fasl (merge-pathnames "unit.fasl" directory))
           (driver (merge-pathnames "run.lisp" directory)))
      (check (and (stringp (first key)) (stringp (second key))) "Missing artifact entry identity")
      (ensure-directories-exist source)
      (unwind-protect
           (progn
             (with-open-file (stream source :direction :output :if-exists :supersede)
               (snowgrave:write-unit-source unit stream))
             (dolist (mode '(:source :fasl))
               (with-open-file (stream driver :direction :output :if-exists :supersede)
                 (let ((*package* (find-package :cl)) (*print-readably* t) (*print-circle* t)
                       (compiled-path (gensym "COMPILED-PATH"))
                       (warnings (gensym "WARNINGS")) (failure (gensym "FAILURE")))
                   (write `(progn
                             ,(if (eq mode :source)
                                  `(load ,(namestring source))
                                  `(multiple-value-bind (,compiled-path ,warnings ,failure)
                                       (compile-file ,(namestring source) :output-file ,(namestring fasl))
                                     (declare (ignore ,warnings))
                                     (assert (not ,failure))
                                     (load ,compiled-path)))
                             (assert (= 42 (funcall (fdefinition (find-symbol ,(second key) ,(first key))) 41)))
                             (assert (equal '(t nil t nil t nil)
                                            (multiple-value-list
                                             (funcall (fdefinition
                                                       (find-symbol ,(second literal-key) ,(first literal-key)))))))
                             (format t "FRESH-ARTIFACT-PASS~%"))
                          :stream stream)))
               ;; Deliberately load neither ASDF nor Snowgrave in the child.
               (multiple-value-bind (output errors status)
                   (uiop:run-program
                    (list "sbcl" "--noinform" "--no-sysinit" "--no-userinit"
                          "--disable-debugger" "--script" (namestring driver))
                    :output :string :error-output :output :ignore-error-status t)
                 (declare (ignore errors))
                 (check (and (zerop status) (search "FRESH-ARTIFACT-PASS" output))
                        "Fresh ~S replay failed (status ~D): ~A" mode status output))))
        (uiop:delete-directory-tree directory :validate t :if-does-not-exist :ignore)))))

(defun rejection-tests ()
  (dolist (source '("((defun entry () (eval '(+ 1 2))))"
                    "((defclass cell () ()) (defun entry () (sxhash (make-instance 'cell))))"
                    "((defclass cell () ())
                       (defun entry ()
                         (let ((object (make-instance 'cell))) (funcall #'sxhash object))))"
                    "((defun entry () (snowgrave.tests::note-event :undeclared)))"))
    (let ((rejected nil))
      (handler-case (make-fixture :rejection source "(entry)" "((entry ()))" "()")
        (snowgrave:snowgrave-error () (setf rejected t)))
      (check rejected "Unsupported source was admitted: ~A" source)))
  ;; The metadata queries return logical descriptors. A native TYPEP on their
  ;; physical DEFSTRUCT representation must not silently change a true answer.
  (dolist (observation
           '("(typep (find-class 'sample) 'class)"
             "(typep (find-class 'sample) 'standard-class)"
             "(typep (find-class 'sample) 'sb-mop:metaobject)"
             "(typep (first (sb-mop:class-slots (find-class 'sample)))
                      'sb-mop:slot-definition)"
             "(typep (first (sb-mop:class-slots (find-class 'sample)))
                      'sb-mop:standard-effective-slot-definition)"
             "(typep (find-class 'sample) '(or null standard-class))"
             "(the standard-class (find-class 'sample))"
             "(let ((class (find-class 'sample)))
                (declare (type standard-class class)) class)"))
    (let ((feature nil))
      (handler-case
          (make-fixture :metadata-type-refusal
                        (format nil "((defclass sample () ((value :initform nil)))
                                      (defun entry () ~A))" observation)
                        "(entry)" "((entry ()))" "()")
        (snowgrave:snowgrave-error (condition)
          (setf feature (snowgrave:error-feature condition))))
      (check (eq feature :physical-type)
             "Metadata observation ~A needs physical-type refusal, got ~S"
             observation feature)))
  (dolist (type '(standard-class (or null standard-class)))
    (let ((feature nil))
      (handler-case
          (make-fixture :metadata-slot-refusal
                        (format nil "((defclass holder () ((class :initarg :class :type ~S)))
                                      (defun entry () (make-instance 'holder :class nil)))" type)
                        "(entry)" "((entry ()))" "()")
        (snowgrave:snowgrave-error (condition)
          (setf feature (snowgrave:error-feature condition))))
      (check (eq feature :slot-type)
             "Physical metadata slot type ~S was admitted, feature ~S" type feature)))
  (dolist (case '(("((defgeneric classify (x))
                     (defmethod classify ((x array)) :array)
                     (defmethod classify ((x sequence)) :sequence)
                     (defun entry (x) (classify x)))"
                  "(array sequence)" (:native-partition :specializer))
                 ("((defgeneric classify (x))
                     (defmethod classify ((x (eql :one))) :one)
                     (defun entry (x) (classify x)))"
                  "(symbol)" (:eql-specializer))
                 ("((defgeneric classify (x))
                     (defmethod classify ((x number)) x)
                     (defmethod classify ((x integer)) (call-next-method (+ x 1)))
                     (defun entry (x) (classify x)))"
                  "(integer number)" (:changed-next-method))
                 ("((defgeneric classify (x))
                     (defmethod classify ((x number)) x)
                     (defmethod classify ((x integer)) (funcall #'call-next-method))
                     (defun entry (x) (classify x)))"
                  "(integer number)" (:next-method-capture))))
    (let ((feature nil))
      (handler-case
          (make-fixture :partition-refusal (first case) "(entry)" "((entry (t)))"
                        "(classify)" :universe (second case))
        (snowgrave:snowgrave-error (condition)
          (setf feature (snowgrave:error-feature condition))))
      (check (member feature (third case)) "Wrong partition refusal: ~S, expected one of ~S" feature (third case))))
  (let ((rejected nil))
    (handler-case
        (snowgrave:close-source-unit '(:forms ((defun unsupported-entry () 7)))
                                     :unit-name (list :unsupported-configuration (incf *fixture-sequence*))
                                     :entries '(unsupported-entry) :external-domains '((unsupported-entry ()))
                                     :native-bindings nil)
      (snowgrave:snowgrave-error () (setf rejected t)))
    (check rejected "Removed configuration declaration was silently accepted")))

(defun run-tests ()
  (let ((*checks* 0))
    (method-linkage-tests)
    (record-tests)
    (dynamic-record-tests)
    (argument-tests)
    (control-tests)
    (binding-tests)
    (native-partition-tests)
    (method-boundary-tests)
    (constant-tests)
    (logical-equalp-tests)
    (logical-metadata-tests)
    (frozen-macro-tests)
    (fresh-artifact-test)
    (rejection-tests)
    (format t "Snowgrave core: ~D checks passed.~%" *checks*)
    t))
