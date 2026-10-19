(in-package #:snowgrave.tests)

(defvar *configured-edge-sequence* 0)
(defun configured-edge-choice () t)
(defvar *configured-edge-opaque* nil)
(defun configured-edge-opaque () *configured-edge-opaque*)

(defun configured-edge-case (tag body expected &key extra (entries '("ENTRY"))
                                                   (calls '("ENTRY" "ENTRY" "ENTRY" "ENTRY"))
                                                   dormant unbound-right writer spare-left spare-payload refusal)
  ;; Distinct native/captured graphs prevent native writes from changing the
  ;; initial state admitted by CLOSE. Assertions exercise only public APIs.
  (let* ((package (make-package (format nil "SNOWGRAVE.CONFIGURED.EDGES.~D" (incf *configured-edge-sequence*))
                                :use '("CL")))
         (*package* package)
         (forms (read-from-string
                 (format nil "((defclass node () ((payload :initarg :payload :reader payload)
                                                  (edge :initarg :edge :reader edge)))
                               (defclass holder () ((left :initarg :left ~A left)
                                                    (right :initarg :right :reader right)
                                                    (spare :initarg :spare :reader spare)
                                                    (dormant :initarg :dormant)))
                               ~A (defun entry (root) ~A))"
                         (if writer ":accessor" ":reader") (or extra "") body)))
         (entry-names (mapcar #'intern entries)) (unit nil) (failure nil))
    (dolist (form forms) (eval form))
    (labels ((node (&optional (value nil valuep))
               (let ((node (if valuep (make-instance (intern "NODE") :payload value)
                               (make-instance (intern "NODE")))))
                 (setf (slot-value node (intern "EDGE")) node) node))
             (graph ()
               (let ((a (node 17)) (b (if unbound-right (node) (node 23))))
                 (make-instance (intern "HOLDER") :left a :right b
                                :spare (cond (spare-left a) (spare-payload (node spare-payload))
                                             (dormant (node)) (t nil))
                                :dormant (when dormant (node)))))
             (observe (function)
               (handler-case (multiple-value-list (catch 'configured-edge-cut (funcall function)))
                 (unbound-slot () '(:unbound-slot)) (simple-error () '(:error)))))
      (let* ((*configured-edge-opaque* (node 31))
             (native-root (graph)) (captured-root (graph))
             (native (loop for name in calls collect (observe (lambda () (funcall (intern name) native-root))))))
        (check (equal expected native))
        (handler-case
            (setf unit
                  (snowgrave:close-source-unit
                   (list :forms forms) :unit-name (list :configured-edge tag *configured-edge-sequence*)
                   :deployment-roots :entries :closed-classes (mapcar #'intern '("NODE" "HOLDER"))
                   :closed-generics
                   (remove-duplicates
                    (append (mapcar #'intern '("PAYLOAD" "EDGE" "LEFT" "RIGHT" "SPARE"))
                            (when writer (list (list 'setf (intern "LEFT"))))
                            (loop for form in forms when (member (first form) '(defgeneric defmethod))
                                    collect (second form))) :test #'equal)
                   :universe (list (intern "NODE") (intern "HOLDER") t)
                   :entries entry-names
                   :external-domains (loop for entry in entry-names collect
                                       (list entry (list (list 'eql captured-root))))
                   :external-operations '(configured-edge-choice configured-edge-opaque)))
          (snowgrave:snowgrave-error (condition) (setf failure condition)))
        (if refusal
            (progn (check (typep failure 'snowgrave:snowgrave-error))
                   (when (keywordp refusal) (check (eq refusal (snowgrave:error-feature failure))))
                   (check (not (null (snowgrave:error-source-key failure)))))
            (progn
              (when failure (error "~S unexpectedly refused: ~A" tag failure))
              (check (null failure))
              (check (equal native
                            (loop for name in calls collect
                              (observe (snowgrave:unit-function unit (intern name) :bind-configuration t)))))))
        failure))))

(defun configured-edge-envelope-tests ()
  (configured-edge-case :read "(payload (left root))" '((17) (17) (17) (17)))
  (let ((swap "(let ((saved (left root)))
                 (setf (slot-value root 'left) (right root)
                       (slot-value root 'right) saved))
               (payload (left root))"))
    (configured-edge-case :swap swap '((23) (17) (23) (17)))
    (configured-edge-case :dormant swap '((23) (17) (23) (17)) :dormant t)
    (configured-edge-case :entries swap '((23) (23) (17) (17))
     :extra "(defun peek (root) (payload (left root)))"
     :entries '("ENTRY" "PEEK") :calls '("ENTRY" "PEEK" "ENTRY" "PEEK")))
  ;; Values supplied by two entries contribute to the same installed field.
  (configured-edge-case :joint-writers
   "(setf (slot-value root 'left) (right root)) 17" '((17) (23) (17) (31) (17) (23))
   :spare-payload 31 :dormant t
   :extra "(defun use-spare (root) (setf (slot-value root 'left) (spare root)) 17)
           (defun peek (root) (payload (left root)))"
   :entries '("ENTRY" "USE-SPARE" "PEEK")
   :calls '("ENTRY" "PEEK" "USE-SPARE" "PEEK" "ENTRY" "PEEK"))
  ;; A completed first store remains visible when later control exits. The
  ;; scalar syntactic continuation isolates field coverage from the existing
  ;; conservative normal-result analysis of unreachable private SETF values.
  (configured-edge-case :throw-prefix
   "(setf (slot-value root 'left) (right root))
    (throw 'snowgrave.tests::configured-edge-cut :cut)
    (setf (slot-value root 'right) (left root)) 17" '((:cut) (23) (23) (23))
   :extra "(defun peek (root) (payload (left root)))"
   :entries '("ENTRY" "PEEK") :calls '("ENTRY" "PEEK" "PEEK" "PEEK"))
  (configured-edge-case :error-prefix
   "(setf (slot-value root 'left) (right root)) (error \"cut\") 17" '((:error) (23) (23) (23))
   :extra "(defun peek (root) (payload (left root)))"
   :entries '("ENTRY" "PEEK") :calls '("ENTRY" "PEEK" "PEEK" "PEEK"))
  (configured-edge-case :secondary-saved
   "(multiple-value-bind (ignored saved) (save-left root)
      (declare (ignore ignored))
      (setf (slot-value root 'left) (right root) (slot-value root 'right) saved))
    (payload (left root))" '((23) (17) (23) (17))
   :extra "(defun save-left (root) (values 0 (left root)))")
  (configured-edge-case :late-default
   "(call-late root) (payload (left root))" '((23) (23) (23) (23))
   :extra "(defun install (root value) (setf (slot-value root 'left) value) 17)
           (defun call-late (root &optional (ignored (install root (right root))))
             (declare (ignore ignored)) 17)")
  (configured-edge-case :recursive-writer
   "(install root 2) (payload (left root))" '((23) (23) (23) (23))
   :extra "(defun install (root count)
             (if (zerop count) (setf (slot-value root 'left) (right root))
                 (install root (1- count))) 17)")
  (configured-edge-case :qualifiers
   "(rotate root) (payload (left root))" '((23) (17) (23) (17))
   :extra "(defgeneric rotate (root))
           (defmethod rotate :around ((root holder))
             (let ((saved (left root))) (call-next-method) (setf (slot-value root 'right) saved)))
           (defmethod rotate :before ((root holder)) (setf (slot-value root 'left) (right root)))
           (defmethod rotate ((root holder)) 17)
           (defmethod rotate :after ((root holder)) (setf (slot-value root 'right) (left root)))")
  ;; The outer place receiver is evaluated before the RHS changes LEFT. Its
  ;; actual A.edge may acquire dormant C; B.edge stays B and PEEK remains safe.
  ;; The first store establishes receiver A on every invocation, even though
  ;; the cross-call LEFT envelope also includes the RHS's transient B value.
  (configured-edge-case :receiver-before-rhs
   "(setf (slot-value root 'left) (spare root))
    (setf (slot-value (left root) 'edge)
          (progn (setf (slot-value root 'left) (right root)) (slot-value root 'dormant))) 17"
   '((17) (23) (17) (23))
   :dormant t :spare-left t :extra "(defun peek (root) (payload (edge (right root))))"
   :entries '("ENTRY" "PEEK") :calls '("ENTRY" "PEEK" "ENTRY" "PEEK"))
  (configured-edge-case :unbind-prefix
   "(slot-makunbound root 'left)
    (throw 'snowgrave.tests::configured-edge-cut :cut)
    (setf (slot-value root 'left) (right root)) 17" '((:cut) (:unbound-slot))
   :extra "(defun peek (root) (payload (left root)))"
   :entries '("ENTRY" "PEEK") :calls '("ENTRY" "PEEK") :refusal :graph-state-slot-read)
  (configured-edge-case :fresh-unbound
   "(setf (slot-value root 'left) (make-instance 'node)) (payload (left root))"
   '((:unbound-slot)) :calls '("ENTRY") :refusal :graph-state-slot-read)
  (configured-edge-case :distinct-same-class-aliases
   "(clear-and-read (left root) (right root))" '((23) (23) (23) (23))
   :extra "(defun clear-and-read (first second)
             (slot-makunbound first 'payload) (payload second))")
  (configured-edge-case :may-store-keeps-other-unbound
   "(let ((target (if (snowgrave.tests::configured-edge-choice) (left root) (right root))))
      (setf (slot-value target 'payload) 31))
    (payload (right root))" '((:unbound-slot)) :unbound-right t
   :calls '("ENTRY") :refusal :graph-state-slot-read)
  ;; No node-qualified invariant is obtained from arbitrary/unvisited
  ;; source writers or a selected generated setter. These preserve the old
  ;; conservative coverage boundary, rather than silently dropping a root.
  (configured-edge-case :unvisited-writer "(payload (left root))" '((17) (17) (17) (17))
   :extra "(defun install (root value) (setf (slot-value root 'left) value) 17)" :refusal t)
  (configured-edge-case :captured-writer
   "(let ((callback #'install)) (declare (ignore callback))) (payload (left root))"
   '((17) (17) (17) (17))
   :extra "(defun install (root value) (setf (slot-value root 'left) value) 17)" :refusal t)
  (configured-edge-case :selected-setter "(payload (left root))" '((17) (17) (17) (17))
   :writer t :refusal t)
  (configured-edge-case :explicit-initialization
   "(initialize-instance root) (payload (left root))" '((17) (17) (17) (17))
   :extra "(defmethod initialize-instance :after ((root holder) &key) (declare (ignore root)))
           (defmethod shared-initialize :after ((root holder) slots &key) (declare (ignore root slots)))"
   :refusal t)
  (configured-edge-case :opaque-replacement
   "(setf (slot-value root 'left) (snowgrave.tests::configured-edge-opaque)) (payload (left root))"
   '((31) (31) (31) (31)) :refusal t)
  (configured-edge-case :may-unbind
   "(let ((target (if (snowgrave.tests::configured-edge-choice) (left root) (right root))))
      (slot-makunbound target 'payload)) 17" '((17) (:unbound-slot))
   :extra "(defun peek (root) (payload (left root)))"
   :entries '("ENTRY" "PEEK") :calls '("ENTRY" "PEEK") :refusal :graph-state-slot-read))
