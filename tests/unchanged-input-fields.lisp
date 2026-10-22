(in-package #:snowgrave.tests)

(defun unchanged-input-field-tests ()
  ;; The input field is an invariant only when the complete normalized cohort
  ;; contains no writer. Loops retain neither a constructor snapshot nor an
  ;; element/content proof. The callback below also exercises unknown effects.
  (dolist (size '(0 3))
    (unchanged-input-reader-loop-test size))
  (relational-state-case :unchanged-input-fresh
    "((defgeneric backing (x))
       (defmethod backing ((x anchor)) (slot-value x 'data))
       (defun walk-fields (x)
         (dotimes (i (length (backing x))) (declare (ignore i)) nil)
         (length (backing x))))"
    "(walk-fields root) (snowgrave.tests::constructor-state-event t) t"
    :expected '(t) :fresh t)
  ;; Native element writes keep the field's container identity. They never
  ;; convert that container's unknown contents into native or cohort data.
  (relational-state-case :unchanged-input-fill
    "((defun walk-fields (x)
         (let ((saved (slot-value x 'data)))
           (dotimes (i 2) (fill saved nil))
           (values (eq saved (slot-value x 'data)) (length (slot-value x 'data))))))"
    "(walk-fields root)" :expected '(t 2))
  (relational-state-case :unchanged-input-private-element
    "((defun walk-fields (x)
         (dotimes (i 1) (setf (svref (slot-value x 'data) i) x))
         (length (slot-value x 'data))))"
    "(walk-fields root)" :unsafe :graph-state-write)
  ;; Each spelling is visited before caller inference, including stores in
  ;; local bodies/defaults and a writer never called by ENTRY. No such source
  ;; can acquire the unchanged-field premise merely by hiding its write.
  (dolist (body
            '("(dotimes (i 1) (slot-makunbound root 'data)) (length (slot-value root 'data))"
              "(dotimes (i 1) (setf (slot-value root 'data) root)) (length (slot-value root 'data))"
              "(rotatef (slot-value root 'data) (slot-value root 'peer)) (length (slot-value root 'data))"
              "(shiftf (slot-value root 'data) (slot-value root 'peer) nil) (length (slot-value root 'data))"
              "(setf (getf (slot-value root 'data) :key) 17) (null (slot-value root 'data))"
              "(setf (getf (getf (slot-value root 'data) :outer) :inner) 17) (null (slot-value root 'data))"
              "(flet ((write-it () (slot-makunbound root 'data))) (write-it)) (length (slot-value root 'data))"
              "(labels ((write-it () (slot-makunbound root 'data))) (write-it)) (length (slot-value root 'data))"
              "(flet ((write-it (&optional (ignored (slot-makunbound root 'data))) (declare (ignore ignored)) nil)) (write-it)) (length (slot-value root 'data))"
              "(let ((write-it (lambda () (slot-makunbound root 'data)))) (funcall write-it)) (length (slot-value root 'data))"
              "(let ((slot (if (snowgrave.tests::relational-state-uncertain) 'peer 'data))) (slot-makunbound root slot)) (length (slot-value root 'data))"
              "(let ((slot (if (snowgrave.tests::relational-state-uncertain) 'peer 'data))) (setf (slot-value root slot) nil)) (length (slot-value root 'data))"
              "(shared-initialize root nil :data root) (length (slot-value root 'data))"
              "(let ((init #'shared-initialize)) (funcall init root nil :data root)) (length (slot-value root 'data))"))
    (relational-state-case (list :unchanged-input-write body)
      "()" body :unsafe t))
  ;; Lexical names are not receiver identity. An unbound same-class peer must
  ;; not borrow the first formal's bound input row after rebinding/selection.
  (dolist (body
            '("(let ((saved root)) (setq root (make-instance 'anchor)) (dotimes (i 0) nil) (length (slot-value root 'data)))"
              "(let ((saved root)) (setq root (make-instance 'anchor)) (slot-makunbound saved 'data) (length (slot-value saved 'data)))"
              "(let ((other (make-instance 'anchor))) (let ((selected (if (snowgrave.tests::relational-state-uncertain) root other))) (dotimes (i 0) nil) (length (slot-value selected 'data))))"))
    (relational-state-case (list :unchanged-input-receiver body) "()" body :unsafe t))
  ;; A selected generated setter/capture remains part of the write inventory.
  (unchanged-input-generated-writer-test)
  (dolist (body '("(setf (getf (slot-value root 'data) :key) 17) (dotimes (i 0) nil) (null (slot-value root 'data))"
                  "(setf (getf (getf (slot-value root 'data) :outer) :inner) 17) (dotimes (i 0) nil) (null (slot-value root 'data))"
                  "(setf (getf (the list (slot-value root 'data)) :key) 17) (dotimes (i 0) nil) (null (slot-value root 'data))"
                  "(setf (getf (values (slot-value root 'data)) :key) 17) (dotimes (i 0) nil) (null (slot-value root 'data))"
                  "(remf (slot-value root 'data) :key) (dotimes (i 0) nil) (null (slot-value root 'data))"
                  "(rotatef (slot-value root 'data) (slot-value root 'peer)) (dotimes (i 0) nil) (length (slot-value root 'data))"
                  "(shiftf (slot-value root 'data) (slot-value root 'peer) nil) (dotimes (i 0) nil) (length (slot-value root 'data))"))
    (unchanged-input-write-case (list :enclosing-place body) body :nil-data t))
  (relational-state-case :unchanged-input-late-helper
    "((defun hidden-writer (x) (slot-makunbound x 'data))
       (defun invoke-writer (x) (hidden-writer x)))"
    "(invoke-writer root) (dotimes (i 0) nil) (length (slot-value root 'data))" :unsafe t)
  (relational-state-case :unchanged-input-helper-default
    "((defun hidden-writer (x &optional (ignored (slot-makunbound x 'data)))
         (declare (ignore ignored)) nil))"
    "(hidden-writer root) (dotimes (i 0) nil) (length (slot-value root 'data))" :unsafe t)
  (relational-state-case :unchanged-input-unknown-writer
    "((defun hidden-writer (x) (slot-makunbound x 'data)))"
    "(snowgrave.tests::relational-state-invoke #'hidden-writer 'anchor)
     (dotimes (i 0) nil) (length (slot-value root 'data))" :unsafe t)
  (unchanged-input-invariant-boundary-tests))

(defun unchanged-input-reader-loop-test (size)
  (let* ((package (make-package (format nil "SNOWGRAVE.UNCHANGED.INPUT.~D"
                                       (incf *constructor-state-sequence*)) :use '("CL")))
         (*package* package)
         (forms (read-from-string
          "((defclass owner () ((data :initarg :data :reader data) (peer :initarg :peer)))
             (defclass words () ((words :initarg :words)))
             (defgeneric fetch (x))
             (defmethod fetch ((x owner)) (length (data x)))
             (defmethod fetch ((x words)) (length (slot-value x 'words)))
             (defgeneric walk (x))
             (defmethod walk ((x owner))
               (dotimes (i (length (data x))) (fetch x)))
             (defmethod walk ((x words))
               (dotimes (i (length (slot-value x 'words))) (fetch x)))
             (defun entry (root) (walk root) (walk (slot-value root 'peer)) 17))"))
         (entry (intern "ENTRY")))
    (mapc #'eval forms)
    (flet ((root () (make-instance (intern "OWNER") :data (make-array size :initial-element nil)
                                  :peer (make-instance (intern "WORDS") :words (vector 5 7)))))
      (let* ((native (root)) (installed (root))
             (unit (snowgrave:close-source-unit
                    (list :forms forms) :unit-name (list :unchanged-input-loop size (incf *constructor-state-sequence*))
                    :closed-classes (mapcar #'intern '("OWNER" "WORDS"))
                    :closed-generics (mapcar #'intern '("DATA" "FETCH" "WALK"))
                    :entries (list entry) :deployment-roots :entries
                    :external-domains (list (list entry (list (list 'eql installed))))
                    :universe (append (mapcar #'intern '("OWNER" "WORDS")) '(vector integer t)))))
        (check (= 17 (funcall entry native)))
        (check (= 17 (funcall (graph-state-fixed unit entry))))
        (initialization-phase-source-check unit)))))

(defun unchanged-input-generated-writer-test ()
  (dolist (body '("(setf (value root) nil) (dotimes (i 0) nil) (length (slot-value root 'data))"
                  "(let ((writer #'(setf value))) (funcall writer nil root)) (dotimes (i 0) nil) (length (slot-value root 'data))"))
    (unchanged-input-write-case (list :generated-writer body) body :writer t)))

(defun unchanged-input-write-case (tag body &key writer nil-data)
  (let* ((package (make-package (format nil "SNOWGRAVE.UNCHANGED.WRITER.~D"
                                       (incf *constructor-state-sequence*)) :use '("CL")))
         (*package* package)
         (forms (read-from-string
                 (format nil "((defclass anchor () ((data :initarg :data ~A) (peer :initarg :peer)))
                                ~A (defun entry (root) ~A))"
                         (if writer ":accessor value" "")
                         (if writer "(defgeneric value (x)) (defgeneric (setf value) (value x))" "") body)))
         (entry (intern "ENTRY")) (anchor (intern "ANCHOR")))
    (mapc #'eval forms)
    (let* ((root (make-instance anchor :data (unless nil-data (vector 17 23))
                                :peer (make-instance anchor :data nil :peer nil))))
      (graph-state-refuses
       (lambda ()
         (snowgrave:close-source-unit
          (list :forms forms) :unit-name (list :unchanged-input-write tag (incf *constructor-state-sequence*))
          :closed-classes (list anchor)
          :closed-generics (when writer (list (intern "VALUE") (list 'setf (intern "VALUE"))))
          :entries (list entry) :deployment-roots :entries
          :external-domains (list (list entry (list (list 'eql root))))
          :universe (list anchor 'vector 'list t)))))))

(defun unchanged-input-invariant-boundary-tests ()
  ;; These are owner-boundary controls, independent of whether a public source
  ;; currently reaches the strongest hypothetical receiver/field combination.
  (let* ((build (snowgrave.sbcl::make-build)) (key (gensym "RECEIVER"))
         (snowgrave.sbcl::*flow-record-origins* `((0 ,key owner nil t (:record-view-classes owner))))
         (snowgrave.sbcl::*flow-input-row*
           (snowgrave.sbcl::make-record-flow-input '(owner)
             '((0 ((data t vector) (peer :unbound :unknown)) owner t (:record-view-classes owner))) nil))
         (domain (list :initializing-record key 'owner)))
    (check (equal '(data t vector nil)
                  (assoc 'data (getf (snowgrave.sbcl::unchanged-record-flow-row build domain) :slots))))
    (check (eq :unbound (second (assoc 'peer (getf (snowgrave.sbcl::unchanged-record-flow-row build domain) :slots)))))
    (check (null (snowgrave.sbcl::unchanged-record-flow-row build (list :initializing-record (gensym) 'owner))))
    (let ((snowgrave.sbcl::*initialization-phase*
            (snowgrave.sbcl::make-initialization-phase
             :relationalp t :records `((0 ,key owner nil t (:record-view-classes owner)))
             :slots '(((:formal 0 data) :pending :pending)))))
      (check (eq :pending (nth-value 0 (snowgrave.sbcl::record-slot-entry-fact build domain 'data)))))
    (setf (snowgrave.sbcl::build-graph-state-invalidations build) '(:writes (data)))
    (check (equal '(data nil :external-result)
                  (assoc 'data (getf (snowgrave.sbcl::unchanged-record-flow-row build domain) :slots))))))
