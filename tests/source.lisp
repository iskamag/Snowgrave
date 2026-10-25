(in-package #:snowgrave.tests)

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
