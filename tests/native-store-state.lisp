(in-package #:snowgrave.tests)

(defun native-store-state-tests ()
  ;; A container's cells are not fields of the record which holds it. The
  ;; direct native store keeps the latter's CURRENT identity/shape/boundness;
  ;; it does not establish any fact about the former's elements.
  (relational-state-case :native-svref-state "()"
    "(setf (svref (slot-value root 'data) 1) 23)
     (snowgrave.tests::constructor-state-event t)
     (eql (length (slot-value root 'data)) 2)" :expected '(t) :fresh t)
  (relational-state-case :native-svref-helper-state
    "((defgeneric backing (x))
       (defmethod backing ((x anchor)) (slot-value x 'data))
       (defun store (x) (setf (svref (backing x) 1) 23) (length (backing x))))"
    "(eql (store root) 2)" :expected '(t))
  (relational-state-case :native-aref-state "()"
    "(let ((saved (slot-value root 'data)))
       (setf (aref (slot-value root 'data)
                   (progn (snowgrave.tests::constructor-state-event :index) 1))
             (progn (snowgrave.tests::constructor-state-event :value) 23))
       (values (eq saved (slot-value root 'data)) (length (slot-value root 'data))))"
    :expected '(t 2))
  (relational-state-case :native-aref-helper-state
    "((defgeneric backing (x))
       (defmethod backing ((x anchor)) (slot-value x 'data))
       (defun store (x) (setf (aref (backing x) 1) 23) (length (backing x))))"
    "(eql (store root) 2)" :expected '(t))
  (relational-state-case :native-aref-private-edge "()"
    "(setf (aref (slot-value root 'data) 1) root) 17" :unsafe :graph-state-write)
  (relational-state-case :native-setter-authored-call "()"
    "(sb-kernel:vector-hairy-data-vector-set/check-bounds (slot-value root 'data) 1 23)"
    :unsafe :call-target)
  (relational-state-case :native-cons-state "()"
    "(let ((pair (cons 17 nil)))
       (setf (car pair) 23 (cdr pair) (list 31))
       (values (length pair) (length (slot-value root 'data))))"
    :expected '(2 2))
  ;; Completed RHS/receiver effects stay in force. The saved native receiver
  ;; cannot justify a later read of a changed or now-unbound record field.
  (relational-state-case :native-store-rhs-unbind "()"
    "(let ((old (slot-value root 'data)))
       (setf (svref old 1) (progn (slot-makunbound root 'data) 23))
       (length (slot-value root 'data)))" :unsafe :graph-state-slot-read)
  (relational-state-case :native-store-rhs-private-replacement "()"
    "(let ((old (slot-value root 'data)))
       (setf (svref old 1) (progn (setf (slot-value root 'data) root) 23))
       (length (slot-value root 'data)))" :unsafe :graph-state-place)
  (relational-state-case :native-store-receiver-effect "()"
    "(let ((old (slot-value root 'data)))
       (setf (svref (prog1 old (slot-makunbound root 'data)) 1) 23)
       (length (slot-value root 'data)))" :unsafe :graph-state-slot-read)
  (relational-state-case :native-array-private-edge "()"
    "(setf (svref (slot-value root 'data) 1) root) 17" :unsafe :graph-state-write)
  (relational-state-case :native-cons-private-edge "()"
    "(let ((pair (cons 17 nil))) (setf (cdr pair) root) (length pair))"
    :unsafe :graph-state-write)
  (relational-state-case :native-array-callable-edge
    "((defun other () 17))"
    "(setf (svref (slot-value root 'data) 1) #'other) 17" :unsafe :graph-state-write)
  ;; GETF is not a direct cell setter: adding a property can write its enclosing
  ;; record place. Keep its conservative transfer instead of reusing old NIL.
  (relational-state-case :native-getf-nested-place "()"
    "(setf (slot-value root 'data) nil)
     (setf (getf (slot-value root 'data) :key) 17)
     (null (slot-value root 'data))" :unsafe :graph-state-slot-read)
  (native-store-shared-effect-tests)
  (native-array-setter-condition-tests)
  (native-store-effect-coverage-tests))

(defun native-store-effect-coverage-tests ()
  ;; Test the transfer boundary directly: an incomplete finite case list is
  ;; not exhaustive when the target's CURRENT coverage is unknown or absent.
  ;; In admitted calls, the existing input-coverage owner separately checks
  ;; all actual rows; this transfer must not invent that premise on its own.
  (dolist (coverage '((:record-view-classes native-store-owner) :unknown :pending nil))
    (let* ((key (gensym "CURRENT-TARGET"))
           (snowgrave.sbcl::*initialization-phase*
             (snowgrave.sbcl::make-initialization-phase
              :relationalp t :records `((0 ,key native-store-owner nil t ,coverage))
              :slots '(((:formal 0 data) nil :external-result))))
           (effects '((0 ((data nil :external-result ((native-store-owner t vector)))))))
           (arguments `((:initializing-record ,key native-store-owner))))
      (snowgrave.sbcl::apply-record-flow-effects (snowgrave.sbcl::make-build) effects arguments nil)
      (let ((field (first (snowgrave.sbcl::initialization-phase-slots snowgrave.sbcl::*initialization-phase*))))
        (if (consp coverage)
            (progn (check (eq t (second field))) (check (eq 'vector (third field))))
            (progn (check (null (second field))) (check (eq :external-result (third field)))))))))

(defun native-store-shared-effect-tests ()
  ;; STORE has one joined ordinary body over ROOT/DATA and WORDS/WORDS.
  ;; Its effect keeps per-class views, including ROOT's bound PEER field and
  ;; WORDS's absent PEER. Replaying it on exact ROOT must project that view;
  ;; copying the unconditional unknown PEER poisons the next actual call.
  (let* ((package (make-package (format nil "SNOWGRAVE.NATIVE.STORE.~D"
                                      (incf *constructor-state-sequence*)) :use '("CL")))
         (forms (constructor-state-read package
                  "((defclass root () ((data :initarg :data) (peer :initarg :peer)))
                     (defclass words () ((words :initarg :words)))
                     (defgeneric backing (x))
                     (defmethod backing ((x root)) (slot-value x 'data))
                     (defmethod backing ((x words)) (slot-value x 'words))
                     (defun store (x) (setf (svref (backing x) 0) 23))
                     (defun entry (root)
                       (store root) (store (slot-value root 'peer))
                       (values (length (backing root))
                               (length (backing (slot-value root 'peer))))))"))
         (root (intern "ROOT" package)) (words (intern "WORDS" package))
         (entry (intern "ENTRY" package)) (backing (intern "BACKING" package)))
    (mapc #'eval forms)
    (flet ((make-root () (make-instance root :data (vector 1 2 3)
                                      :peer (make-instance words :words (vector 5 7)))))
      (let* ((native (make-root)) (installed (make-root))
             (unit (graph-state-close
                    :native-store-shared-effect forms (list entry)
                    (list (list entry (list (list 'eql installed)))) :generics (list backing))))
        (check (equal '(3 2) (multiple-value-list (funcall entry native))))
        (check (equal '(3 2) (multiple-value-list (funcall (graph-state-fixed unit entry)))))
        (initialization-phase-source-check unit)
        (check (not (search ":RECORD-VIEW-CLASSES"
                            (with-output-to-string (stream) (snowgrave:write-unit-source unit stream)))))))))

(defun native-array-setter-condition-tests ()
  ;; The native condition retains the receiver array. Import that exact array
  ;; so the comparison checks its identity as well as the index/type payload
  ;; and cleanup ordering, rather than comparing unrelated private copies.
  (let* ((package (make-package (format nil "SNOWGRAVE.NATIVE.SETTER.~D"
                                      (incf *constructor-state-sequence*)) :use '("CL")))
         (forms (constructor-state-read package
                  "((defclass root () ((data :initarg :data)))
                     (defun entry (root)
                       (unwind-protect (setf (aref (slot-value root 'data) 99) 23)
                         (snowgrave.tests::constructor-state-event :cleanup))))"))
         (root (intern "ROOT" package)) (entry (intern "ENTRY" package)))
    (mapc #'eval forms)
    (let* ((array (vector 1 2)) (native (make-instance root :data array))
           (installed (make-instance root :data array))
           (unit (graph-state-close
                  :native-array-setter-condition forms (list entry)
                  (list (list entry (list (list 'eql installed))))
                  :resources (list (list :backing array)) :external '(constructor-state-event)))
           (observation (constructor-state-observation (lambda () (funcall entry native)) nil))
           (closed (constructor-state-observation (graph-state-fixed unit entry) nil)))
      (check (eq :error (first observation)))
      (check (equal observation closed))
      (check (equal '(:cleanup) (getf closed :events)))
      (check (equalp #(1 2) array)))))
