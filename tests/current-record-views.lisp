(in-package #:snowgrave.tests)

(defun current-record-view-tests ()
  ;; Class selection may use the CURRENT conditional view, but an ordinary
  ;; helper still has only its unconditional field proof before selection.
  (let ((disjoint
          "(defgeneric data (x)) (defgeneric words (x))
           (defclass left () ((data :initform (vector 17 23) :reader data)))
           (defclass right () ((words :initform (vector 31) :reader words)))
           (defgeneric measure (x))
           (defmethod measure ((x left)) (length (data x)))
           (defmethod measure ((x right)) (length (words x)))"))
    (relational-state-case :current-generated-readers
      (format nil "(~A (defun read-owner (x) (measure x)))" disjoint)
      "(declare (ignore root))
       (values (read-owner (make-instance 'left)) (read-owner (make-instance 'right)))"
      :expected '(2 1))
    (relational-state-case :current-unconditional-read
      "((defclass left () ((data :initform (vector 17 23))))
         (defclass right () ((words :initform (vector 31))))
         (defun read-owner (x) (length (slot-value x 'data))))"
      "(declare (ignore root)) (read-owner (make-instance 'left)) (read-owner (make-instance 'right))"
      :unsafe :graph-state-operation-input))
  (let ((shared
          "(defclass left () ((data :initarg :data :initform (vector 17 23))))
           (defclass right () ((data :initarg :data :initform (vector 31))))
           (defgeneric measure (x))
           (defmethod measure ((x left)) (length (slot-value x 'data)))
           (defmethod measure ((x right)) (length (slot-value x 'data)))"))
    (relational-state-case :current-same-class-private
      (format nil "(~A (defun read-owner (x) (measure x)))" shared)
      "(read-owner (make-instance 'left)) (read-owner (make-instance 'left :data root))"
      :unsafe :graph-state-operation-input)
    (relational-state-case :current-write-before-selection
      (format nil "(~A (defun read-owner (x bad) (setf (slot-value x 'data) bad) (measure x)))" shared)
      "(read-owner (make-instance 'left) root) (read-owner (make-instance 'right) root)"
      :unsafe :graph-state-operation-input)
    (relational-state-case :current-unbind-before-selection
      (format nil "(~A (defun read-owner (x) (slot-makunbound x 'data) (measure x)))" shared)
      "(declare (ignore root)) (read-owner (make-instance 'left)) (read-owner (make-instance 'right))"
      :unsafe :graph-state-operation-input)
    (relational-state-case :current-branch-unbind
      (format nil "(~A (defun read-owner (x)
                         (when (snowgrave.tests::relational-state-uncertain) (slot-makunbound x 'data))
                         (measure x)))" shared)
      "(declare (ignore root)) (read-owner (make-instance 'left)) (read-owner (make-instance 'right))"
      :unsafe :graph-state-operation-input)
    (relational-state-case :current-must-alias-store
      (format nil "(~A (defun read-owner (x alias bad)
                         (setf (slot-value alias 'data) bad) (measure x)))" shared)
      "(let ((a (make-instance 'left)) (b (make-instance 'right)))
         (read-owner a a root) (read-owner b b root))"
      :unsafe :graph-state-operation-input)
    (relational-state-case :current-may-alias-unbind
      (format nil "(~A (defun read-owner (x alias) (slot-makunbound alias 'data) (measure x)))" shared)
      "(declare (ignore root))
       (let ((a (make-instance 'left)) (b (make-instance 'left)))
         (read-owner a a) (read-owner a b))"
      :unsafe :graph-state-operation-input)
    (relational-state-case :current-unknown-helper-effects
      (format nil "(~A (defun read-owner (x)
                         (flet ((clear () (slot-makunbound x 'data))) (clear)) (measure x)))" shared)
      "(declare (ignore root)) (read-owner (make-instance 'left)) (read-owner (make-instance 'right))"
      :unsafe :graph-state-operation-input)
    (relational-state-case :current-late-opaque-caller
      (format nil "(~A (defun read-owner (x) (measure x)))" shared)
      "(read-owner (make-instance 'left))
       (read-owner (snowgrave.tests::relational-state-invoke #'identity 'right))"
      :unsafe :graph-state-generic-authority)
    (relational-state-case :current-native-mixed-caller
      (format nil "(~A (defmethod measure ((x vector)) (length x))
                        (defun read-owner (x) (measure x)))" shared)
      "(declare (ignore root)) (read-owner (make-instance 'left)) (read-owner (vector 1 2))"
      :unsafe :graph-state-operation-input)
    ;; The source class belongs to the field selector. The target is LEFT,
    ;; while the value comes from the RIGHT peer, whose DATA is private.
    (relational-state-case :current-peer-source-class
      "((defclass left () ((data :initform (vector 17 23))))
        (defclass right () ((data :initarg :data)))
        (defgeneric measure (x))
        (defmethod measure ((x left)) (length (slot-value x 'data)))
        (defmethod measure ((x right)) (declare (ignore x)) 0)
        (defgeneric copy-data (x y))
        (defmethod copy-data ((x left) (y right)) (setf (slot-value x 'data) (slot-value y 'data)) nil)
        (defmethod copy-data ((x right) (y left)) (declare (ignore x y)) nil)
        (defmethod copy-data ((x left) (y left)) (declare (ignore x y)) nil)
        (defmethod copy-data ((x right) (y right)) (declare (ignore x y)) nil)
        (defun read-owner (x y) (copy-data x y) (measure x)))"
      "(let ((a (make-instance 'left)) (b (make-instance 'right :data root)))
         (read-owner a b) (read-owner b a))"
      :unsafe :graph-state-operation-input))
  (relational-state-case :current-same-class-unbound
    "((defclass left () ((data :initarg :data)))
       (defgeneric measure (x))
       (defmethod measure ((x left)) (length (slot-value x 'data)))
       (defun read-owner (x) (measure x)))"
    "(declare (ignore root))
     (read-owner (make-instance 'left :data (vector 1 2))) (read-owner (make-instance 'left))"
    :unsafe :graph-state-operation-input)
  (relational-state-case :current-multidispatch
    "((defclass left () ((data :initform (vector 17 23))))
       (defclass right () ((words :initform (vector 31))))
       (defgeneric measure (x y))
       (defmethod measure ((x left) (y right))
         (+ (length (slot-value x 'data)) (length (slot-value y 'words))))
       (defmethod measure ((x right) (y left))
         (+ (length (slot-value x 'words)) (length (slot-value y 'data))))
       (defmethod measure ((x left) (y left))
         (+ (length (slot-value x 'data)) (length (slot-value y 'data))))
       (defmethod measure ((x right) (y right))
         (+ (length (slot-value x 'words)) (length (slot-value y 'words))))
       (defun read-owner (x y) (measure x y)))"
    "(declare (ignore root)) (let ((a (make-instance 'left)) (b (make-instance 'right)))
       (values (read-owner a b) (read-owner b a)))"
    :expected '(3 3))
  (relational-state-case :current-multiple-inheritance
    "((defclass left () ((data :initform (vector 17 23))))
       (defclass right () ((words :initform (vector 31))))
       (defclass both (left right) ())
       (defgeneric measure (x))
       (defmethod measure ((x left)) (length (slot-value x 'data)))
       (defmethod measure ((x right)) (length (slot-value x 'words)))
       (defun read-owner (x) (measure x)))"
    "(declare (ignore root))
     (values (read-owner (make-instance 'left)) (read-owner (make-instance 'right))
             (read-owner (make-instance 'both)))"
    :expected '(2 1 2))
  (relational-state-case :current-empty-multiple-inheritance
    "((defclass left () ()) (defclass right () ()) (defclass both (left right) ())
       (defgeneric measure (x))
       (defmethod measure ((x left)) (declare (ignore x)) 17)
       (defmethod measure ((x right)) (declare (ignore x)) 23)
       (defun read-owner (x) (measure x)))"
    "(declare (ignore root))
     (values (read-owner (make-instance 'left)) (read-owner (make-instance 'right))
             (read-owner (make-instance 'both)))"
    :expected '(17 23 17))
  (current-record-view-algebra-tests)
  (current-record-view-class-coverage-tests))

(defun current-record-view-class-coverage-tests ()
  ;; Empty fields cannot encode the difference between exact LEFT and a
  ;; nominal LEFT input that also admits the sealed MI subclass BOTH.
  (let* ((package (make-package (format nil "SNOWGRAVE.CURRENT.CLASSES.~D"
                                      (incf *constructor-state-sequence*)) :use '("CL")))
         (forms (constructor-state-read
                 package "((defclass left () ()) (defclass right () ()) (defclass both (left right) ()))"))
         (classes (mapcar #'second forms))
         (build (snowgrave.sbcl::make-build :source (snowgrave:make-authored-source forms)
                                           :open-package package
                                           :layouts (mapcar (lambda (class) (list :class class :slots nil)) classes)))
         (left (first classes)) (both (third classes)))
    (dolist (form forms)
      (eval `(defclass ,(snowgrave.sbcl::mapped-name (second form) package)
                 ,(mapcar (lambda (class) (snowgrave.sbcl::mapped-name class package)) (third form)) ())))
    (let* ((exact (snowgrave.sbcl::make-call-record-flow-input build (list (list :owned-record left))))
           (nominal (snowgrave.sbcl::make-call-record-flow-input build (list left)))
           (exact-row (first (snowgrave.sbcl::record-flow-input-records exact)))
           (nominal-row (first (snowgrave.sbcl::record-flow-input-records nominal)))
           (joined (snowgrave.sbcl::join-record-flow-inputs build exact nominal)))
      (check (null (second exact-row)))
      (check (null (second nominal-row)))
      (check (equal (list :record-view-classes left) (fifth exact-row)))
      (check (member both (rest (fifth nominal-row))))
      (check (member both (rest (fifth (first (snowgrave.sbcl::record-flow-input-records joined))))))
      (check (not (snowgrave.sbcl::record-view-domain-covered-p build (fifth nominal-row) (fifth exact-row)))))))

(defun current-record-view-algebra-tests ()
  ;; A joined peer has LEFT/native and RIGHT/private current views. The
  ;; target's LEFT class supplies no information about the peer's class.
  ;; Exercise the summary boundary directly as well as the public fixtures:
  ;; unrelated conservative rejection must not hide an unsound substitution.
  (let* ((build (snowgrave.sbcl::make-build))
         (left 'current-view-left) (right 'current-view-right)
         (target (gensym "TARGET")) (peer (gensym "PEER"))
         (private (list :graph-node 7 left))
         (target-coverage (list :record-view-classes left))
         (peer-coverage (list :record-view-classes left right))
         (before `((0 ((data t vector ((,left t vector)))))
                   (1 ((data t :external-result ((,left t vector) (,right t ,private)))))))
         (arguments `((:initializing-record ,target ,left) (:initializing-record ,peer (or ,left ,right)))))
    (dolist (selector (list (list :field 1 'data) (list :field 1 'data right)))
      (let* ((value (list :relational-value selector :external-result))
             (snowgrave.sbcl::*initialization-phase*
               (snowgrave.sbcl::make-initialization-phase
                :relationalp t
                :records `((0 ,target ,left nil t ,target-coverage)
                           (1 ,peer (or ,left ,right) nil t ,peer-coverage))
                :slots `(((:formal 0 data) t vector ((,left t vector)))
                         ((:formal 1 data) t :external-result ((,left t vector) (,right t ,private)))))))
        (snowgrave.sbcl::apply-record-flow-effects
         build `((0 ((data t ,value ((,left t ,value)))) ,left nil ,target-coverage)) arguments before)
        (let* ((field (first (snowgrave.sbcl::initialization-phase-slots snowgrave.sbcl::*initialization-phase*)))
               (actual (third (assoc left (fourth field)))))
          (check (equal (if (fourth selector) private :external-result) actual)))))
    (check (snowgrave.sbcl::record-view-domain-covered-p build '(:record-view-classes) target-coverage))
    (check (not (snowgrave.sbcl::record-view-domain-covered-p build :unknown target-coverage)))
    (check (snowgrave.sbcl::record-view-domain-covered-p build :pending target-coverage))
    (check (eq :unknown (snowgrave.sbcl::select-record-view-domain build :unknown left left (list left))))
    (check (not (snowgrave.sbcl::record-field-cases-covered-p
                 build '(data nil :external-result) `(data nil :external-result ((,left t vector))) :unknown)))))
