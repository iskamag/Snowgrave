(in-package #:snowgrave.tests)

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
        (closer-mop:set-funcallable-instance-function
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

(defun argument-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :arguments
       "((defclass cell () ((value :initarg :value :reader value)))
          (defgeneric combine (object &optional amount &rest rest &key offset))
          (defmethod combine ((object cell) &optional (amount 3 suppliedp) &rest rest &key (offset 5))
            (values (+ (value object) (or amount 0) offset) (not (null suppliedp)) rest))
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
    ;; CCL 1.13 compiles CALL-NEXT-METHOD outside its lexical scope in a native
    ;; optional initform. Check the specified result independently on that host.
    (compare-entry unit package "DEFAULT-NEXT" '(5) '((16) nil) :native-p #-ccl t #+ccl nil)))

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
              (error (condition) (values (not (null (typep condition 'error))) t))))
          (defun no-next ()
            (handler-case (only-integer 3)
              (error (condition) (values (not (null (typep condition 'error))) t))))
          (defun text-result () (greeting 3)))"
       "(missing no-next text-result)" "((missing ()) (no-next ()) (text-result ()))"
       "(only-integer greeting)" :universe "(integer)")
    (dolist (name '("MISSING" "NO-NEXT"))
      (let ((observation (compare-entry unit package name nil)))
        (check (second (first observation)) "~A did not take its condition path" name)))
    (compare-entry unit package "TEXT-RESULT" nil '(("hello") nil))))
