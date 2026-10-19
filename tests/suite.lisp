(defpackage #:snowgrave.tests
  (:use #:cl)
  (:export #:run-tests))

(defpackage #:snowgrave.fixture
  (:use #:cl)
  (:shadowing-import-from #:snowgrave #:defclass #:defgeneric #:defmethod))

(in-package #:snowgrave.tests)

(defvar *checks* 0)
(defvar *external-log* nil)
(defvar *injected-compiler-capture* nil)
(defun test-unit-function (unit name)
  (snowgrave:unit-function unit (if (symbolp name) (symbol-name name) name)))
(defun test-code-function (unit name)
  (snowgrave.artifact-tests:artifact-function (snowgrave:unit-metadata unit)
                                           (if (symbolp name) (symbol-name name) name)))
(defun proof-name (proof)
  (let ((key (getf proof :function-key)))
    (second (if (eq (car key) 'setf) (second key) key))))
(defun compiler-capture-operation (x) x)
(cl:defgeneric external-operation (x))
(cl:defmethod external-operation ((x number))
  (push (list :external x) *external-log*)
  (values (* 2 x) :external-value))
(cl:defgeneric (setf external-cell) (value cell))
(cl:defmethod (setf external-cell) (value cell)
  (push (list :writer value (car cell)) *external-log*)
  (rplaca cell value)
  (values value :external-value))
(defmacro check (expression)
  `(progn (incf *checks*)
          (unless ,expression (error "Check failed: ~S" ',expression))))

(defmacro signals (type &body body)
  `(check (handler-case (progn ,@body nil) (,type () t))))

(defun fixture-forms ()
  (let ((*package* (find-package :snowgrave.fixture)))
    (read-from-string
     "((defclass policy () ((value :accessor value)))
        (defclass fast (policy) ())
        (defparameter *log* nil)
        (defgeneric account (p n))
        (defmethod account :around ((p policy) (n number))
          (push :around-enter *log*)
          (unwind-protect (call-next-method) (push :around-exit *log*)))
        (defmethod account :before ((p policy) (n number)) (push :before *log*))
        (defmethod account :after ((p policy) (n number)) (push :after *log*))
        (defmethod account ((p policy) (n number)) (push :primary *log*) (values (+ n (value p)) :tag))
        (defmethod account ((p fast) (n number)) (push :fast *log*) (call-next-method))
        (defparameter *captured* (load-time-value #'account))
        (defun run (p n) (funcall (load-time-value #'account) p n))
        (defun log-values () (reverse *log*))
        (defun write-value (p v) (setf (value p) v))
        (defun write-slot (p v) (setf (slot-value p 'value) v))
        (defun increment-slot (p n) (incf (slot-value p 'value) n))
        (defun bound-state (p) (slot-boundp p 'value))
        (defun unbind (p) (slot-makunbound p 'value))
        (defun scoped-log (p n)
          (let ((*log* nil)) (run p n) (reverse *log*))))")))

(defun close-fixture (&optional (identity '(fixture :version 1)) (forms (fixture-forms)))
  (let ((*package* (find-package :snowgrave.fixture)))
    (snowgrave:close-source-unit
     (list :forms forms) :unit-name identity
     :closed-classes (read-from-string "(policy fast)")
     :universe (read-from-string "(policy fast number)")
     :closed-generics (read-from-string "(account value (setf value))")
     :entries (read-from-string "(run log-values write-value write-slot increment-slot bound-state unbind scoped-log)")
     :external-domains (read-from-string "((run (policy number)) (log-values ()) (write-value (policy t)) (write-slot (policy t)) (increment-slot (policy number)) (bound-state (policy)) (unbind (policy)) (scoped-log (policy number)))")
     :external-operations nil)))

(defun record-tests ()
  (let* ((layout (snowgrave:make-layout '(record :version 1) 'record '(record ancestor) '(a b)))
         (record (snowgrave:sg-make-record layout)))
    (check (snowgrave:sg-record-p record))
    (check (eq (snowgrave:sg-record-class record) (snowgrave:sg-record-class record)))
    (check (not (eq (snowgrave:sg-record-class record) 'record)))
    (check (eq (snowgrave:sg-record-class record)
               (snowgrave:sg-record-class
                (snowgrave:sg-make-record (snowgrave:make-layout '(record :version 1) 'record '(record ancestor) '(a b))))))
    (check (not (eq (snowgrave:sg-record-class record)
                    (snowgrave:sg-record-class
                     (snowgrave:sg-make-record (snowgrave:make-layout '(record :version 2) 'record '(record ancestor) '(a b)))))))
    (check (snowgrave:sg-record-typep record 'ancestor))
    (check (not (snowgrave:sg-record-boundp record 'a)))
    (let ((condition (handler-case (snowgrave:sg-record-read record 'a) (unbound-slot (c) c))))
      (check (typep condition 'unbound-slot))
      (check (eq (unbound-slot-instance condition) record))
      (check (eq (cell-error-name condition) 'a)))
    (check (null (snowgrave:sg-record-write record 'a nil)))
    (check (snowgrave:sg-record-boundp record 'a))
    (check (null (snowgrave:sg-record-read record 'a)))
    (check (null (snowgrave:sg-record-unbind record 'a)))
    (check (not (snowgrave:sg-record-boundp record 'a)))
    (signals error (snowgrave:sg-record-boundp record 'absent)))
  ;; A caller's accepted slot vector must not rename an existing record's
  ;; fields after the logical layout has been constructed.
  (let* ((slots (vector 'a 'b))
         (layout (snowgrave:make-layout '(owned-slots :version 1) 'record '(record ancestor) slots))
         (record (snowgrave:sg-make-record layout))
         (class (snowgrave:sg-record-class record)))
    (snowgrave:sg-record-write record 'a 17)
    (snowgrave:sg-record-write record 'b 29)
    (setf (aref slots 0) 'replacement (aref slots 1) 'a)
    (check (= (snowgrave:sg-record-read record 'a) 17))
    (check (= (snowgrave:sg-record-read record 'b) 29))
    (check (snowgrave:sg-record-boundp record 'a))
    (check (snowgrave:sg-record-boundp record 'b))
    (check (eq class (snowgrave:sg-record-class record)))
    (check (snowgrave:sg-record-layout-p record '(owned-slots :version 1) 'record '(record ancestor) '(a b)))
    (signals error (snowgrave:sg-record-read record 'replacement))))

(defun unit-tests ()
  (let* ((native-methods (mapcar (lambda (class) (copy-list (sb-mop:specializer-direct-methods (find-class class)))) '(t number)))
         (unit (close-fixture))
         (metadata (snowgrave:unit-metadata unit))
         (class (find "FAST" (getf metadata :record-layouts)
                      :key (lambda (x) (symbol-name (getf x :class))) :test #'string=))
         (layout (snowgrave:make-layout (getf class :identity) (getf class :class)
                                       (getf class :ancestors) (getf class :slots)
                                        :error-mapping (getf class :error-mapping)))
         (record (snowgrave:sg-make-record layout)))
    (check (every (lambda (difference)
                    (every (lambda (method)
                             (let ((name (sb-mop:generic-function-name (sb-mop:method-generic-function method))))
                               ;; Compiling constant SLOT-VALUE sites lazily
                               ;; creates host global slot helpers. Authored
                               ;; private GFs and classes must not remain.
                               (and (consp name) (eq (car name) 'sb-pcl::slot-accessor)
                                    (every (lambda (specializer)
                                             (symbol-package (sb-mop:class-name specializer)))
                                           (sb-mop:method-specializers method))))) difference))
                  (mapcar (lambda (class previous)
                            (set-exclusive-or previous (sb-mop:specializer-direct-methods (find-class class)) :test #'eq))
                          '(t number) native-methods)))
    (snowgrave:sg-record-write record (intern "VALUE" :snowgrave.fixture) 3)
    (progv (list (intern "*LOG*" :snowgrave.fixture)) (list '(:external))
      (check (equal (funcall (test-unit-function unit 'scoped-log) record 7)
                    '(:around-enter :before :fast :primary :after :around-exit)))
      (check (equal (symbol-value (intern "*LOG*" :snowgrave.fixture)) '(:external)))
      (funcall (test-unit-function unit 'run) record 7)
      (check (eq (car (last (symbol-value (intern "*LOG*" :snowgrave.fixture)))) :external)))
    (check (equal (multiple-value-list (funcall (test-unit-function unit 'run) record 7)) '(10 :tag)))
    (check (equal (funcall (test-unit-function unit 'log-values))
                  '(:around-enter :before :fast :primary :after :around-exit)))
    (signals snowgrave:domain-violation (funcall (test-unit-function unit 'run) :outside 7))
    (check (not (typep (test-unit-function unit 'run) 'generic-function)))
    (check (getf (snowgrave:unit-report unit) :second-pass-fresh))
    (check (not (getf (snowgrave:unit-report unit) :target-accepted)))
    (check (= (funcall (test-unit-function unit 'write-value) record 5) 5))
    (check (funcall (test-unit-function unit 'bound-state) record))
    (check (eq (funcall (test-unit-function unit 'unbind) record) record))
    (check (not (funcall (test-unit-function unit 'bound-state) record)))
    (signals unbound-slot (funcall (test-unit-function unit 'run) record 7))
    (check (null (funcall (test-unit-function unit 'write-slot) record nil)))
    (check (funcall (test-unit-function unit 'bound-state) record))
    (check (= (funcall (test-unit-function unit 'write-slot) record 8) 8))
    (check (= (funcall (test-unit-function unit 'increment-slot) record 3) 11))
    (snowgrave:sg-record-write record (intern "VALUE" :snowgrave.fixture) 3)
    (let ((other (snowgrave:sg-make-record
                  (snowgrave:make-layout '(other-unit) (getf class :class) (getf class :ancestors) (getf class :slots)))))
      (signals snowgrave:domain-violation (funcall (test-unit-function unit 'run) other 7)))
    ;; A public logical layout must match the frozen schema, not merely its
    ;; claimed unit/class name. These invalid records must fail at the entry.
    (dolist (description (list (list :identity (list (getf class :identity) :changed-version)
                                     :ancestors (getf class :ancestors) :slots (getf class :slots))
                              (list :identity (getf class :identity)
                                    :ancestors (list (getf class :class)) :slots (getf class :slots))
                              (list :identity (getf class :identity)
                                    :ancestors (getf class :ancestors) :slots nil)))
      (let ((forged (snowgrave:sg-make-record
                     (snowgrave:make-layout (getf description :identity) (getf class :class)
                                            (getf description :ancestors) (getf description :slots)
                                            :error-mapping (getf class :error-mapping)))))
        (signals snowgrave:domain-violation (funcall (test-unit-function unit 'run) forged 7))))
    (signals snowgrave:unsupported-definition (close-fixture))
    (let ((unmapped (snowgrave:sg-make-record
                     (snowgrave:make-layout (getf class :identity) (getf class :class)
                                            (getf class :ancestors) (getf class :slots)))))
      (signals snowgrave:domain-violation (funcall (test-unit-function unit 'run) unmapped 7)))
    (check (search ":ABI-VERSION 3" (with-output-to-string (s) (snowgrave:write-unit-metadata unit s))))
    (check (not (search "SNOWGRAVE.BUILDER" (with-output-to-string (s) (snowgrave:write-unit-source unit s)))))
    ;; Neither successful nor failed closure mutates authored function cells.
    (check (not (fboundp (intern "ACCOUNT" :snowgrave.fixture))))
    (let ((before (remove-if-not (lambda (p) (search "SNOWGRAVE.BUILDER." (package-name p))) (list-all-packages))))
      (signals snowgrave:unclosed-call
        (close-fixture '(rejected :version 1)
                       (append (replace-entry-body (fixture-forms) "RUN"
                                                   (list (intern "ESCAPE" :snowgrave.fixture)))
                               (list (list 'defun (intern "ESCAPE" :snowgrave.fixture) nil '(eval '(+ 1 2)))))))
      (check (equal before (remove-if-not (lambda (p) (search "SNOWGRAVE.BUILDER." (package-name p))) (list-all-packages)))))))

(defun replace-entry-body (forms name body)
  (mapcar (lambda (form)
            (if (and (eq (car form) 'defun) (symbolp (cadr form)) (string= (symbol-name (cadr form)) name))
                (append (subseq form 0 3) (list body)) form)) forms))

(defun domain-rejection-tests ()
  (let ((*package* (find-package :snowgrave.fixture)))
    (dolist (body '("(account \"outside\" n)"
                    "(funcall (lambda (p) (account p n)) \"outside\")"))
      (signals snowgrave:incomplete-domain
        (close-fixture (list 'bad-internal body)
                       (replace-entry-body (fixture-forms) "RUN" (read-from-string body)))))
    (progv (list (intern "*LOG*" *package*)) (list '(:must-survive-failed-close))
      (signals snowgrave:incomplete-domain
        (close-fixture '(failed-staged-globals)
                       (replace-entry-body (fixture-forms) "RUN" (read-from-string "(account \"outside\" n)"))))
      (check (equal (symbol-value (intern "*LOG*" *package*)) '(:must-survive-failed-close))))
    (signals snowgrave:unsupported-definition
      (close-fixture '(bad-capture)
                     (replace-entry-body (fixture-forms) "RUN"
                                         (read-from-string "(setq *captured* #'value)"))))
    (signals snowgrave:unclosed-call
      (close-fixture '(unknown-dynamic-capture)
                     (replace-entry-body (fixture-forms) "RUN"
                                         (read-from-string "(let ((*captured* (car *log*))) (funcall *captured* p n))"))))
    (signals snowgrave:unclosed-call
      (close-fixture '(mutable-callable-special)
                     (replace-entry-body (fixture-forms) "RUN" (read-from-string "(funcall *captured* p n)"))))
    (signals snowgrave:unclosed-call
      (close-fixture '(symbol-capture)
                     (replace-entry-body (fixture-forms) "RUN" (read-from-string "(funcall (load-time-value 'account) p n)"))))
    (dolist (body '("(mapcar 'account (list p) (list n))"
                    "(find p (list p) :test 'equal)"
                    "(snowgrave:sg-record-read p 'value)"))
      (signals snowgrave:unclosed-call
        (close-fixture (list 'unclosed-physical-call body)
                       (replace-entry-body (fixture-forms) "RUN" (read-from-string body)))))
    (dolist (body '("(typep p '(or policy fast))"
                    "(slot-value n 'value)"
                    "(print p)"
                    "(equalp (list p) (list p))"
                    "(make-hash-table :test 'equalp)"
                    "(gethash p (car *log*))"
                    "(setf (gethash p (car *log*)) n)"
                    "(find (list p) (list (list p)) :test #'equalp)"))
      (signals snowgrave:unclosed-class-operation
        (close-fixture (list 'unclosed-physical-observation body)
                       (replace-entry-body (fixture-forms) "RUN" (read-from-string body)))))))

(defun record-observation-tests ()
  (let* ((*package* (find-package :snowgrave.fixture))
         (unit (close-fixture '(record-observation :version 1)
                              (replace-entry-body (fixture-forms) "RUN"
                                                  (read-from-string "(values (equalp p p) (equalp p (make-instance 'fast)) (typep p 'policy) (typep p 'fast))"))))
         (description (find (intern "FAST" *package*) (getf (snowgrave:unit-metadata unit) :record-layouts)
                            :key (lambda (layout) (getf layout :class))))
         (record (snowgrave:sg-make-record
                  (snowgrave:make-layout (getf description :identity) (getf description :class)
                                        (getf description :ancestors) (getf description :slots)
                                        :error-mapping (getf description :error-mapping)))))
    (check (equal (multiple-value-list (funcall (test-unit-function unit 'run) record 0)) '(t nil t t)))))

(defpackage #:snowgrave.equality.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass))

(defun indirect-record-equality-tests ()
  (let* ((*package* (find-package :snowgrave.equality.fixture))
         (prefix (read-from-string
                  "((defclass sample () ((x :initform 17)))
                     (defparameter *effects* nil)
                     (defun other (x y) (declare (ignore x y)) :other))"))
         (cases '("(equalp p q)" "(funcall #'equalp p q)" "(apply #'equalp (list p q))"
                  "(multiple-value-call #'equalp (values p) (values q))"
                  "(let ((tail (identity nil))) (apply #'equalp p q tail))"
                  "(let ((f #'equalp)) (values (eq f #'equalp) (funcall f p q)))"
                  "(funcall #'equalp p p)" "(apply #'equalp p (list p))"
                  "(multiple-value-call #'equalp (values p p))"
                  "(funcall #'equalp \"abc\" \"ABC\")"
                  "(apply #'equalp (list 17 17.0))"
                  "(funcall (progn (push :callee *effects*) (if flag #'equalp #'other))
                            (progn (push :left *effects*) p)
                            (progn (push :right *effects*) q))"
                  "(apply (progn (push :callee *effects*) (if flag #'equalp #'other))
                          (progn (push :left *effects*) p)
                          (progn (push :right *effects*) q)
                          (progn (push :tail *effects*) nil))"
                  "(multiple-value-call (progn (push :callee *effects*) (if flag #'equalp #'other))
                       (values (progn (push :left *effects*) p))
                       (values (progn (push :right *effects*) q)))"))
         (entries (loop for index below (length cases) collect (intern (format nil "EQUALITY-~D" index))))
         (forms (append prefix
                        (loop for expression in cases for entry in entries collect
                          `(defun ,entry (,(intern "FLAG"))
                             (setq ,(intern "*EFFECTS*") nil)
                             (let ((,(intern "P") (make-instance ',(intern "SAMPLE")))
                                   (,(intern "Q") (make-instance ',(intern "SAMPLE"))))
                               (list (multiple-value-call #'list ,(read-from-string expression))
                                     (reverse ,(intern "*EFFECTS*"))))))))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(indirect-record-equality)
                :closed-classes (list (intern "SAMPLE")) :universe (list (intern "SAMPLE") 'number 'symbol)
                :entries entries :external-domains (mapcar (lambda (entry) (list entry '(symbol))) entries))))
    (dolist (form forms) (eval form))
    (dolist (entry entries)
      (dolist (flag '(t nil))
        (check (equal (funcall (fdefinition entry) flag) (funcall (snowgrave:unit-function unit entry) flag)))))
    ;; The same operation cannot recurse into a lowered record aggregate through
    ;; a different call syntax and acquire native structural equality silently.
    (dolist (expression '("(funcall #'equalp (list p) (list q))"
                          "(apply #'equalp (list (list p) (list q)))"
                          "(multiple-value-call #'equalp (values (list p)) (values (list q)))"))
      (let ((entry (intern "BAD-EQUALITY")))
        (signals snowgrave:unclosed-class-operation
          (snowgrave:close-source-unit
           (list :forms (append prefix
                                (list `(defun ,entry ()
                                         (let ((,(intern "P") (make-instance ',(intern "SAMPLE")))
                                               (,(intern "Q") (make-instance ',(intern "SAMPLE"))))
                                           ,(read-from-string expression))))))
           :unit-name (list 'bad-indirect-equality expression) :closed-classes (list (intern "SAMPLE"))
           :universe (list (intern "SAMPLE")) :entries (list entry) :external-domains (list (list entry nil))))))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-indirect-equality.lisp" root))
           (data (merge-pathnames ".build/fresh-indirect-equality.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream data :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh indirect record equality executed."
                     (uiop:run-program
                      (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                            (namestring (merge-pathnames "scripts/fresh-indirect-equality.lisp" root))
                            (namestring source) (namestring data)) :output :string))))))

(defpackage #:snowgrave.operation.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass))

(defun observe-higher-record (x y)
  (declare (ignore x))
  (typep y 'standard-object))

(defun indirect-operation-tests ()
  (let* ((*package* (find-package :snowgrave.operation.fixture))
         (prefix (read-from-string "((defclass sample () ()) (defparameter *effects* nil))"))
         (cases
           '("(funcall (progn (push :callee *effects*) #'format)
                       (progn (push :destination *effects*) nil)
                       (progn (push :control *effects*) control)
                       (progn (push :data *effects*) 17))"
             "(apply (progn (push :callee *effects*) #'format)
                     (progn (push :destination *effects*) nil)
                     (progn (push :control *effects*) control)
                     (list (progn (push :data *effects*) 17)))"
             "(multiple-value-call (progn (push :callee *effects*) #'format)
                (values (progn (push :destination *effects*) nil)
                        (progn (push :control *effects*) control))
                (values (progn (push :data *effects*) 17)))"
             "(funcall (progn (push :callee *effects*) #'mapcar)
                       (progn (push :callback *effects*) #'identity)
                       (progn (push :sequence *effects*) (list 17 18)))"
             "(apply (progn (push :callee *effects*) #'mapcar)
                     (progn (push :callback *effects*) #'identity)
                     (list (progn (push :sequence *effects*) (list 17 18))))"
             "(multiple-value-call (progn (push :callee *effects*) #'mapcar)
                (values (progn (push :callback *effects*) #'identity))
                (values (progn (push :sequence *effects*) (list 17 18))))"
             "(funcall (progn (push :callee *effects*) #'gethash)
                       (progn (push :key *effects*) 17)
                       (progn (push :table *effects*) table)
                       (progn (push :default *effects*) :missing))"
             "(apply (progn (push :callee *effects*) #'gethash)
                     (list (progn (push :key *effects*) 17)
                           (progn (push :table *effects*) table)
                           (progn (push :default *effects*) :missing)))"
             "(multiple-value-call (progn (push :callee *effects*) #'gethash)
                (values (progn (push :key *effects*) 17)
                        (progn (push :table *effects*) table))
                (values (progn (push :default *effects*) :missing)))"
             "(funcall (progn (push :callee *effects*) #'mapcar)
                       (progn (push :callback *effects*)
                              (if (zerop (length control)) #'abs #'identity))
                       (progn (push :sequence *effects*) (list -17 18)))"
             "(let ((tail (identity nil)))
                (apply (progn (push :callee *effects*) #'mapcar)
                       (progn (push :callback *effects*) #'identity)
                       (progn (push :sequence *effects*) (list 17 18))
                       tail))"))
         (entries (loop for index below (length cases) collect (intern (format nil "OPERATION-~D" index))))
         (forms (append prefix
                        (loop for expression in cases for entry in entries collect
                          `(defun ,entry (,(intern "CONTROL") ,(intern "TABLE"))
                             (setq ,(intern "*EFFECTS*") nil)
                             (list (multiple-value-call #'list ,(read-from-string expression))
                                   (reverse ,(intern "*EFFECTS*")))))))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(shared-indirect-operation-contracts)
                :closed-classes (list (intern "SAMPLE")) :universe (list (intern "SAMPLE") 'string 'hash-table)
                :entries entries :external-domains (mapcar (lambda (entry) (list entry '(string hash-table))) entries))))
    (dolist (form forms) (eval form))
    (dolist (entry entries)
      (dolist (present '(nil t))
        (let ((ordinary (make-hash-table)) (closed (make-hash-table)))
          (when present (setf (gethash 17 ordinary) :present (gethash 17 closed) :present))
          (check (equal (funcall entry "~S" ordinary)
                        (funcall (snowgrave:unit-function unit entry) "~S" closed))))))
    (let ((entry (nth 9 entries)))
      (check (equal (funcall entry "" (make-hash-table))
                    (funcall (snowgrave:unit-function unit entry) "" (make-hash-table)))))
    (labels ((refuse (expression type feature &optional externals)
               (let* ((entry (intern "BAD-OPERATION"))
                      (body (read-from-string expression))
                      (condition
                        (handler-case
                            (snowgrave:close-source-unit
                             (list :forms (append prefix
                                                  (list `(defun ,entry (,(intern "CONTROL") ,(intern "TABLE"))
                                                           (let ((,(intern "P") (make-instance ',(intern "SAMPLE")))
                                                                 (,(intern "Q") (make-instance ',(intern "SAMPLE"))))
                                                             ,body)))))
                             :unit-name (list 'refused-indirect-operation expression)
                             :closed-classes (list (intern "SAMPLE"))
                             :universe (list (intern "SAMPLE") 'string 'hash-table)
                             :external-operations externals
                             :entries (list entry) :external-domains (list (list entry '(string hash-table))))
                          (snowgrave:snowgrave-error (condition) condition))))
                 (check (typep condition type))
                 (check (eq feature (snowgrave:error-feature condition))))))
      (dolist (expression '("(format nil control p)" "(funcall #'format nil control p)"
                            "(apply #'format (list nil control p))"
                            "(multiple-value-call #'format (values nil control) (values p))"
                            "(mapcar #'print (list p))"
                            "(funcall #'mapcar #'print (list p))"
                            "(apply #'mapcar (list #'print (list p)))"
                            "(multiple-value-call #'mapcar (values #'print (list p)))"))
        (refuse expression 'snowgrave:unclosed-class-operation :printed-record-or-metaobject))
      (dolist (expression '("(find (list p) (list (list q)) :test #'equalp)"
                            "(funcall #'find (list p) (list (list q)) :test #'equalp)"
                            "(apply #'find (list (list p) (list (list q)) :test #'equalp))"
                            "(multiple-value-call #'find (values (list p) (list (list q))) (values :test #'equalp))"))
        (refuse expression 'snowgrave:unclosed-class-operation :equalp-callback))
      (dolist (expression '("(make-hash-table :test 'equalp)"
                            "(funcall #'make-hash-table :test 'equalp)"
                            "(apply #'make-hash-table (list :test 'equalp))"
                            "(multiple-value-call #'make-hash-table (values :test 'equalp))"))
        (refuse expression 'snowgrave:unclosed-class-operation :equalp-hash-table))
      (dolist (expression '("(gethash p table)" "(funcall #'gethash p table)"
                            "(apply #'gethash (list p table))"
                            "(multiple-value-call #'gethash (values p table))"))
        (refuse expression 'snowgrave:unclosed-class-operation :record-hash-table-domain))
      (dolist (expression '("(find p (list q) (if control :test :key) #'equalp)"
                            "(funcall #'find p (list q) (if control :test :key) #'equalp)"
                            "(apply #'find (list p (list q) (if control :test :key) #'equalp))"
                            "(multiple-value-call #'find (values p (list q) (if control :test :key) #'equalp))"))
        (refuse expression 'snowgrave:unclosed-call :callback-target))
      (dolist (expression '("(make-hash-table (if control :test :size) 'equalp)"
                            "(funcall #'make-hash-table (if control :test :size) 'equalp)"
                            "(apply #'make-hash-table (list (if control :test :size) 'equalp))"
                            "(multiple-value-call #'make-hash-table (values (if control :test :size) 'equalp))"))
        (refuse expression 'snowgrave:unclosed-call :hash-table-test))
      (refuse "(let ((tail (identity (list (list q)))))
                 (apply #'mapcar #'snowgrave.tests::observe-higher-record (list 17) tail))"
              'snowgrave:unclosed-call :external-callback-representation '(observe-higher-record)))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-indirect-operation.lisp" root))
           (data (merge-pathnames ".build/fresh-indirect-operation.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream data :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh indirect operation contracts executed."
                     (uiop:run-program
                      (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                            (namestring (merge-pathnames "scripts/fresh-indirect-operation.lisp" root))
                            (namestring source) (namestring data)) :output :string))))))

(defpackage #:snowgrave.mapping.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass))

(defun mapping-equality-tests ()
  (let* ((*package* (find-package :snowgrave.mapping.fixture))
         (prefix (read-from-string
                  "((defclass sample () ())
                    (defclass child (sample) ())
                    (defparameter *effects* nil)
                    (defun fresh-record () (make-instance 'sample))
                    (defun choose-callback (flag) (if flag #'equalp #'eq))
                    (defun observe-callback (callback left right)
                      (list (eq callback #'equalp) (length left) (length right))))"))
         (cases
           '("(mapcar #'equalp (list p p) (list p q))"
             "(mapcar #'equalp (list 17 p) (list q p))"
             "(mapcar #'equalp
                (progn (push :left *effects*) (if flag (list p q) (list q p)))
                (progn (push :right *effects*) (list p q)))"
             "(let ((result (mapc (progn (push :callback *effects*) #'equalp)
                                 (progn (push :left *effects*) (list p p))
                                 (progn (push :right *effects*) (list p q)))))
                (list (eq p (car result)) (eq p (cadr result)) (length result)))"
             "(funcall (progn (push :callee *effects*) #'mapcar)
                       (progn (push :callback *effects*) #'equalp)
                       (progn (push :left *effects*) (list p p))
                       (progn (push :right *effects*) (list p q)))"
             "(apply (progn (push :callee *effects*) #'mapcar)
                     (progn (push :callback *effects*) #'equalp)
                     (list (progn (push :left *effects*) (list p p))
                           (progn (push :right *effects*) (list p q))))"
             "(apply (progn (push :callee *effects*) #'mapcar)
                     (list (progn (push :callback *effects*) #'equalp)
                           (progn (push :left *effects*) (list p p))
                           (progn (push :right *effects*) (list p q))))"
             "(apply (progn (push :callee *effects*) #'mapcar)
                     (progn (push :callback *effects*) #'equalp)
                     (progn (push :left *effects*) (list p p))
                     (list (progn (push :right *effects*) (list p q))))"
             "(multiple-value-call (progn (push :callee *effects*) #'mapcar)
                (values)
                (values (progn (push :callback *effects*) #'equalp)
                        (progn (push :left *effects*) (list p p)))
                (values)
                (values (progn (push :right *effects*) (list p q))))"
             "(multiple-value-call (progn (push :callee *effects*) #'mapcar)
                (values (progn (push :callback *effects*) (values #'equalp :discarded)))
                (values (progn (push :left *effects*) (list p p)))
                (values (progn (push :right *effects*) (list p q))))"
             "(mapcar (progn (push :callback *effects*) (if flag #'equalp #'eq))
                      (list p p) (list p q))"
             "(funcall #'mapcar (choose-callback flag) (list p p) (list p q))"
             "(mapcar (choose-callback flag) (list p p) (list p q))"
             "(mapcar (if flag #'equalp #'eq) (list \"A\" 17) (list \"a\" 17.0))"
             "(funcall (progn (push :callee *effects*)
                             (if flag #'mapcar #'observe-callback))
                       (progn (push :callback *effects*) #'equalp)
                       (progn (push :left *effects*) (list p p))
                       (progn (push :right *effects*) (list p q)))"
             "(apply (if flag #'mapcar #'observe-callback)
                     (list #'equalp (list p p) (list p q)))"
             "(multiple-value-call (if flag #'mapcar #'observe-callback)
                (values #'equalp (list p p)) (values (list p q)))"
             "(mapcar #'equalp (list (fresh-record) p) (list (fresh-record) p))"
             "(mapcar #'equalp (list (if flag p q) p) (list p p p))"
             "(let ((result (funcall #'mapc #'equalp (list p p) (list p q))))
                (list (eq p (car result)) (eq p (cadr result)) (length result)))"
             "(let ((result (apply #'mapc (list #'equalp (list p p) (list p q)))))
                (list (eq p (car result)) (eq p (cadr result)) (length result)))"
             "(let ((result (multiple-value-call #'mapc
                              (values #'equalp (list p p)) (values (list p q)))))
                (list (eq p (car result)) (eq p (cadr result)) (length result)))"
             "(mapcar #'equalp (list p) nil)"
             ;; P's first list is evaluated before P changes. The other
             ;; sequence still contains proven records, so identity is exact.
             "(mapcar #'equalp (list p)
                      (progn (setq p (list 17)) (list q)))"
             "(mapcar (progn (push :callback *effects*) #'equalp)
                      (progn (push :left *effects*) (list p))
                      (progn (push :right *effects*) (setq p (list 17)) (list q)))"))
         (entries (loop for index below (length cases) collect (intern (format nil "MAPPING-~D" index))))
         (forms (append prefix
                        (loop for expression in cases for entry in entries collect
                          `(defun ,entry (,(intern "FLAG"))
                             (setq ,(intern "*EFFECTS*") nil)
                             (let ((,(intern "P") (make-instance ',(intern "SAMPLE")))
                                   (,(intern "Q") (make-instance ',(intern "CHILD"))))
                               (values ,(read-from-string expression)
                                       (reverse ,(intern "*EFFECTS*")) :secondary))))))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(mapping-record-equality)
                :closed-classes (list (intern "SAMPLE") (intern "CHILD"))
                :universe (list (intern "SAMPLE") (intern "CHILD") t)
                :entries entries :external-domains (mapcar (lambda (entry) (list entry '(t))) entries))))
    (dolist (form forms) (eval form))
    (let ((expected
            (loop for entry in entries collect
              (loop for flag in '(nil t) collect
                (let ((ordinary (multiple-value-list (funcall entry flag))))
                  (check (equal ordinary (multiple-value-list (funcall (snowgrave:unit-function unit entry) flag))))
                  (list flag ordinary))))))
      (labels ((refuse (expression feature)
                 (let ((condition
                         (handler-case
                             (snowgrave:close-source-unit
                              (list :forms (append prefix
                                                   (list `(defun ,(intern "BAD-MAPPING") (,(intern "FLAG"))
                                                            (let ((,(intern "P") (make-instance ',(intern "SAMPLE")))
                                                                  (,(intern "Q") (make-instance ',(intern "SAMPLE"))))
                                                              ,(read-from-string expression))))))
                              :unit-name (list 'refused-mapping-equality expression)
                              :closed-classes (list (intern "SAMPLE") (intern "CHILD"))
                              :universe (list (intern "SAMPLE") (intern "CHILD") t)
                              :entries (list (intern "BAD-MAPPING"))
                              :external-domains (list (list (intern "BAD-MAPPING") '(t))))
                           (snowgrave:snowgrave-error (condition) condition))))
                   (check (typep condition 'snowgrave:snowgrave-error))
                   (check (or (eq feature (snowgrave:error-feature condition))
                              (error "Mapping ~S expected refusal ~S, received ~A"
                                     expression feature condition))))))
        (dolist (expression '("(maplist #'equalp (list p) (list q))"
                              "(mapcar #'equalp (list (list p)) (list (list q)))"
                              "(let ((tail (identity (list (list q)))))
                                 (apply #'mapcar #'equalp (list p) tail))"))
          (refuse expression :equalp-callback))
        (refuse "(mapcar (if flag #'equalp 17) (list p) (list q))" :callback-target)
        (refuse "(mapcar (choose-callback flag) (list p))" :compiler-failure)
        (refuse "(mapcar (choose-callback flag) (list p) (list q) (list p))" :compiler-failure))
      (let* ((root (asdf:system-source-directory "snowgrave"))
             (source (merge-pathnames ".build/fresh-mapping-equality.lisp" root))
             (data (merge-pathnames ".build/fresh-mapping-equality.metadata" root))
             (observations (merge-pathnames ".build/fresh-mapping-equality.expected" root)))
        (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
        (with-open-file (stream data :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
        (with-open-file (stream observations :direction :output :if-exists :supersede) (write expected :stream stream :readably t))
        (check (search "Fresh mapping record equality executed."
                       (uiop:run-program
                        (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                              (namestring (merge-pathnames "scripts/fresh-mapping-equality.lisp" root))
                              (namestring source) (namestring data) (namestring observations)) :output :string)))))))

(defpackage #:snowgrave.keyword.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass))

(defun keyword-equality-tests ()
  (let* ((*package* (find-package :snowgrave.keyword.fixture))
         (prefix (read-from-string
                  "((defclass sample () ())
                    (defclass child (sample) ())
                    (defparameter *effects* nil)
                    (defun fresh-record () (make-instance 'sample))
                    (defun choose-test (flag) (if flag #'equalp #'eq))
                    (defun observe-key (value) (push :key *effects*) value)
                    (defun observe-test (item sequence &key test)
                      (declare (ignore item sequence)) (eq test #'equalp)))"))
         (cases
           '("(eq p (find p (list q p p) :test #'equalp))"
             "(position p (list q p p) :test #'equalp)"
             "(count p (list q p p) :test #'equalp)"
             "(position p (vector q p p) :test #'equalp)"
             "(count p (vector q p p) :test-not #'equalp)"
             "(count p \"pp\" :test #'equalp)"
             "(find p (list (fresh-record)) :test #'equalp)"
             "(funcall #'find p (list (fresh-record)) :test #'equalp)"
             "(apply #'find (list p (list (fresh-record)) :test #'equalp))"
             "(multiple-value-call #'find (values p (list (fresh-record))) (values :test #'equalp))"
             "(count p (list q p p) :test-not #'equalp)"
             "(eq q (find p (list p q p) :test-not #'equalp))"
             "(let* ((sequence (list q p p)) (tail (member p sequence :test #'equalp)))
                (list (eq tail (cdr sequence)) (eq (car tail) p)))"
             "(cdr (assoc p (list (cons q 1) (cons p 2)) :test #'equalp))"
             "(let ((result (remove p (list p q p) :test #'equalp)))
                (list (length result) (eq (car result) q)))"
             "(let ((result (delete p (list p q p) :test #'equalp)))
                (list (length result) (eq (car result) q)))"
             "(let ((result (remove p (list p q p) :test-not #'equalp)))
                (list (length result) (eq (car result) p) (eq (cadr result) p)))"
             "(count (progn (push :item *effects*) p)
                     (progn (push :sequence *effects*) (list q p p))
                     :test (progn (push :test *effects*) #'equalp)
                     :key (progn (push :key-function *effects*) #'observe-key))"
             "(count p (list q p p q) :from-end t :start 1 :end 3
                     :test #'equalp :key #'observe-key)"
             "(funcall (progn (push :callee *effects*) #'count)
                       (progn (push :item *effects*) p)
                       (progn (push :sequence *effects*) (list q p p))
                       :test (progn (push :test *effects*) (values #'equalp :discarded)))"
             "(apply (progn (push :callee *effects*) #'count)
                     (progn (push :item *effects*) p)
                     (list (progn (push :sequence *effects*) (list q p p))
                           :test (progn (push :test *effects*) #'equalp)))"
             "(apply #'count (list (progn (push :item *effects*) p)
                                  (progn (push :sequence *effects*) (list q p p))
                                  :test (progn (push :test *effects*) #'equalp)))"
             "(apply #'count p (list q p p) :test (list #'equalp))"
             "(apply #'count p (list q p p) :test #'equalp '())"
             "(multiple-value-call (progn (push :callee *effects*) #'count)
                (values) (values (progn (push :item *effects*) p))
                (values (progn (push :sequence *effects*) (list q p p)) :test)
                (values) (values (progn (push :test *effects*) (values #'equalp :discarded))))"
             "(count p (list q p p) :test (if flag #'equalp #'eq))"
             "(count p (list q p p) :test (choose-test flag))"
             "(funcall (if flag #'count #'observe-test) p (list q p p) :test #'equalp)"
             "(apply (if flag #'count #'observe-test) (list p (list q p p) :test #'equalp))"
             "(multiple-value-call (if flag #'count #'observe-test)
                (values p (list q p p)) (values :test #'equalp))"
             "(count p (list q p p)
                     :test (progn (push :first-test *effects*) #'equalp)
                     :test (progn (push :ignored-test *effects*) #'eq))"
             "(count p (list q p p)
                     :test (progn (push :first-test *effects*) #'eq)
                     :test (progn (push :ignored-test *effects*) #'equalp))"
             "(count p nil :test #'equalp :key #'observe-key)"
             "(count (fresh-record) (list p q) :test #'equalp)"
             "(position (if flag p q) (list p q) :test #'equalp)"
             "(equal (find \"A\" (list \"a\" \"b\") :test #'equalp) \"a\")"
             "(count 17 (list 17.0 18 17) :test #'equalp)"
             "(apply #'position (list 17 (list 17.0 18) :test #'equalp))"))
         (entries (loop for index below (length cases) collect (intern (format nil "KEYWORD-~D" index))))
         (forms (append prefix
                        (loop for expression in cases for entry in entries collect
                          `(defun ,entry (,(intern "FLAG"))
                             (setq ,(intern "*EFFECTS*") nil)
                             (let ((,(intern "P") (make-instance ',(intern "SAMPLE")))
                                   (,(intern "Q") (make-instance ',(intern "CHILD"))))
                               (values ,(read-from-string expression)
                                       (reverse ,(intern "*EFFECTS*")) :secondary))))))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(keyword-record-equality)
                :closed-classes (list (intern "SAMPLE") (intern "CHILD"))
                :universe (list (intern "SAMPLE") (intern "CHILD") t)
                :entries entries :external-domains (mapcar (lambda (entry) (list entry '(t))) entries))))
    (dolist (form forms) (eval form))
    (let ((expected
            (loop for entry in entries collect
              (loop for flag in '(nil t) collect
                (let ((ordinary (multiple-value-list (funcall entry flag))))
                  (check (equal ordinary (multiple-value-list (funcall (snowgrave:unit-function unit entry) flag))))
                  (list flag ordinary))))))
      (labels ((refuse (expression feature &optional externals)
                 (let ((condition
                         (handler-case
                             (snowgrave:close-source-unit
                              (list :forms (append (if externals (subseq prefix 0 3) prefix)
                                                   (list `(defun ,(intern "BAD-KEYWORD") (,(intern "FLAG"))
                                                            (let ((,(intern "P") (make-instance ',(intern "SAMPLE")))
                                                                  (,(intern "Q") (make-instance ',(intern "SAMPLE"))))
                                                              ,(read-from-string expression))))))
                              :unit-name (list 'refused-keyword-equality expression)
                              :external-operations externals
                              :closed-classes (list (intern "SAMPLE") (intern "CHILD"))
                              :universe (list (intern "SAMPLE") (intern "CHILD") t)
                              :entries (list (intern "BAD-KEYWORD"))
                              :external-domains (list (list (intern "BAD-KEYWORD") '(t))))
                           (snowgrave:snowgrave-error (condition) condition))))
                   (check (typep condition 'snowgrave:snowgrave-error))
                   (check (or (eq feature (snowgrave:error-feature condition))
                              (error "Keyword ~S expected refusal ~S, received ~A"
                                     expression feature condition))))))
        (refuse "(count (list p) (list (list q)) :test #'equalp)" :equalp-callback)
        (refuse "(count p (list q) :test (if flag #'equalp 17))" :callback-target)
        (refuse "(count p (list q) :test #'equalp :test-not #'equalp)" :compiler-failure)
        (refuse "(apply #'count p (list q) (identity (list :test #'equalp)))" :callback-target)
        ;; Invalidating P's class fact prevents an item-based identity proof.
        ;; This keyword consumer does not infer a sequence-element proof.
        (refuse "(count p (progn (setq p (list 17)) (list q)) :test #'equalp)" :equalp-callback)
        (refuse "(count 17 (list q) :test #'equalp :key #'identity)" :equalp-callback)
        (refuse "(count p q :test #'equalp)" :callback-sequence-domain)
        (refuse "(count p (list q) :test #'snowgrave.tests::observe-higher-record)"
                :external-callback-representation '(observe-higher-record)))
      (let* ((root (asdf:system-source-directory "snowgrave"))
             (source (merge-pathnames ".build/fresh-keyword-equality.lisp" root))
             (data (merge-pathnames ".build/fresh-keyword-equality.metadata" root))
             (observations (merge-pathnames ".build/fresh-keyword-equality.expected" root)))
        (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
        (with-open-file (stream data :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
        (with-open-file (stream observations :direction :output :if-exists :supersede) (write expected :stream stream :readably t))
        (check (search "Fresh keyword record equality executed."
                       (uiop:run-program
                        (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                              (namestring (merge-pathnames "scripts/fresh-keyword-equality.lisp" root))
                              (namestring source) (namestring data) (namestring observations)) :output :string)))))))

(defun method-capture-tests ()
  (let* ((*package* (find-package :snowgrave.fixture))
         (forms (read-from-string
                 "((defgeneric captured-identity (x))
                    (defgeneric captured-wrapper (x))
                    (defmethod captured-identity ((x t)) x)
                    (defmethod captured-wrapper ((x t))
                      (funcall (load-time-value #'captured-identity) x))
                    (defun captured-entry (x) (captured-wrapper x)))"))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(method-capture :version 1)
                :closed-generics (read-from-string "(captured-wrapper captured-identity)")
                :entries (read-from-string "(captured-entry)")
                :external-domains (read-from-string "((captured-entry (t)))"))))
    (check (eq (funcall (test-unit-function unit 'captured-entry) :capture) :capture))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-capture.lisp" root))
           (metadata (merge-pathnames ".build/fresh-capture.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede)
        (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede)
        (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh method capture executed."
                     (uiop:run-program (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                                             (namestring (merge-pathnames "scripts/fresh-capture.lisp" root))
                                             (namestring source) (namestring metadata)) :output :string))))))

(defun unbound-special-tests ()
  (let* ((*package* (find-package :snowgrave.fixture))
         (forms (read-from-string "((defvar *unbound-source*) (defun read-unbound () *unbound-source*))"))
         (unit (snowgrave:close-source-unit (list :forms forms) :unit-name '(unbound-special :version 1)
                                            :entries (read-from-string "(read-unbound)")
                                            :external-domains (read-from-string "((read-unbound ()))")))
         (condition (handler-case (funcall (test-unit-function unit 'read-unbound)) (unbound-variable (c) c))))
    (check (typep condition 'unbound-variable))
    (check (eq (cell-error-name condition) (intern "*UNBOUND-SOURCE*" :snowgrave.fixture)))))

(defun external-operation-tests ()
  ;; The paper explicitly permits a declared host generic outside the cohort.
  ;; Its call remains external and keeps every value and effect in its trace.
  (let* ((forms '((defun external-entry (x) (external-operation x))))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(external-boundary :version 1)
                :universe '(number) :entries '(external-entry)
                :external-domains '((external-entry (number)))
                :external-operations '(external-operation)))
         (metadata (snowgrave:unit-metadata unit))
         (*external-log* nil))
    (dolist (form forms) (eval form))
    (let ((open-values (multiple-value-list (external-entry 21)))
          (open-effects (copy-list *external-log*)))
      (setf *external-log* nil)
      (check (equal open-values (multiple-value-list (funcall (test-unit-function unit 'external-entry) 21))))
      (check (equal open-effects *external-log*)))
    (check (equal (getf (first (getf metadata :external-operations)) :lambda-list) '(x)))
    (check (equal (getf (getf (snowgrave:unit-report unit) :declaration) :external-operations)
                  '(external-operation)))))

(defun external-writer-tests ()
  ;; The former arbitrary caller-owned T/T crossing had no representation
  ;; proof. Keep it as a permanent refusal rather than assume opaque contents
  ;; cannot contain a lowered record or relocated callable.
  (let ((condition
          (handler-case
              (snowgrave:close-source-unit
               '(:forms ((defun opaque-external-writer (cell value) (setf (external-cell cell) value))))
               :unit-name '(opaque-external-writer) :universe '(t) :entries '(opaque-external-writer)
               :external-domains '((opaque-external-writer (t t)))
               :external-operations '((setf external-cell)))
            (snowgrave:unclosed-call (condition) condition))))
    (check (typep condition 'snowgrave:unclosed-call))
    (check (eq (snowgrave:error-feature condition) :external-value-representation)))
  (let* ((forms
           '((defun external-writer-entry (seed value) (setf (external-cell (list seed)) value))
             (defun external-writer-call (seed value) (funcall #'(setf external-cell) value (list seed)))
             (defun lexical-writer-entry (cell value)
               (flet (((setf external-cell) (value cell)
                        (setf (car cell) (list :local value)) (values value :local-value)))
                 (setf (external-cell cell) value)))
             (defun lexical-writer-call (cell value)
               (flet (((setf external-cell) (value cell)
                        (setf (car cell) (list :local value)) (values value :local-value)))
                 (funcall #'(setf external-cell) value cell)))))
         (entries (mapcar #'second forms))
         (writer '(setf external-cell))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(external-and-lexical-writers)
                :universe '(t number) :entries entries
                :external-domains (loop for entry in entries for index from 0
                                        collect (list entry (if (< index 2) '(number number) '(t t))))
                :external-operations (list writer))))
    (dolist (form forms) (eval form))
    (check (eq (getf (snowgrave:unit-report unit) :claim) :semantically-closed))
    (check (equal (getf (first (getf (snowgrave:unit-metadata unit) :external-operations)) :identity) writer))
    (check (member (snowgrave::function-name-key writer)
                   (getf (snowgrave:unit-report unit) :dependencies) :test #'equal))
    (dolist (entry entries)
      (let* ((*external-log* nil) (native-cell (list 0)) (closed-cell (list 0))
             (externalp (member entry (subseq entries 0 2)))
             (native-values (multiple-value-list (funcall entry (if externalp 0 native-cell) 7)))
             (native-effects (copy-tree *external-log*)))
        (setf *external-log* nil)
        (check (equal native-values (multiple-value-list (funcall (snowgrave:unit-function unit entry) (if externalp 0 closed-cell) 7))))
        (check (equal native-cell closed-cell))
        (check (equal native-effects *external-log*))))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-external-writers.lisp" root))
           (data (merge-pathnames ".build/fresh-external-writers.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream data :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh external and lexical writers executed."
               (uiop:run-program
                (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                      (namestring (merge-pathnames "scripts/fresh-external-writers.lisp" root))
                      (namestring source) (namestring data)) :output :string))))))

(defpackage #:snowgrave.sequence-result.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defgeneric #:defmethod))

(defpackage #:snowgrave.external-value.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass #:defgeneric #:defmethod))

(defun external-value-representation-tests ()
  (let* ((*package* (find-package :snowgrave.external-value.fixture))
         (sample (intern "SAMPLE" *package*)) (value (intern "VALUE" *package*))
         (entry (intern "ENTRY" *package*)) (captured (intern "*CAPTURED*" *package*))
         (record-observer (intern "RECORD-OBSERVER" *package*))
         (aggregate-observer (intern "AGGREGATE-OBSERVER" *package*))
         (callable-observer (intern "CALLABLE-OBSERVER" *package*))
         (state-observer (intern "STATE-OBSERVER" *package*)))
    (eval (read-from-string "(defvar *captured*)"))
    (eval (read-from-string "(defun record-observer (x) (typep (if (consp x) (car x) x) 'standard-object))"))
    (eval (read-from-string "(defun callable-observer (x) (typep x 'generic-function))"))
    (eval (read-from-string "(defun aggregate-observer () (typep (car *captured*) 'standard-object))"))
    (eval (read-from-string "(defun state-observer () (typep *captured* 'generic-function))"))
    (eval (read-from-string "(defun function-observer () #'value)"))
    (eval (read-from-string "(defun parameter-observer () (typep (symbol-value 'parameter) 'standard-object))"))
    (labels ((reject (forms classes generics universe external feature)
               (dolist (form forms) (eval form))
               (let ((ordinary (funcall entry))
                     (before (symbol-value captured)))
                 (check ordinary)
                 (let ((condition
                         (handler-case
                             (snowgrave:close-source-unit
                              (list :forms forms) :unit-name (list 'external-value feature forms)
                              :closed-classes classes :closed-generics generics :universe universe
                              :entries (list entry) :external-domains (list (list entry nil))
                              :external-operations (list external))
                           (snowgrave:unclosed-call (condition) condition))))
                   (check (typep condition 'snowgrave:unclosed-call))
                   (check (eq (snowgrave:error-feature condition) feature))
                   (check (eq before (symbol-value captured)))))))
      (setf (symbol-value captured) :original)
      ;; Each ordinary call sees its actual authored CLOS object. The old
      ;; unchanged-host-binding lowering returned NIL while claiming closure.
      (dolist (body '("(record-observer (make-instance 'sample))"
                      "(funcall #'record-observer (make-instance 'sample))"
                      "(apply #'record-observer (list (make-instance 'sample)))"
                      "(multiple-value-call #'record-observer (values (make-instance 'sample)))"
                      "(record-observer (list (make-instance 'sample)))"))
        (reject (append (read-from-string "((defclass sample () ()))")
                        (list (list 'defun entry nil (read-from-string body))))
                (list sample) nil (list sample) record-observer :external-value-representation))
      (reject (read-from-string "((defclass sample () ())
                                  (defun entry () (mapcar #'record-observer (list (make-instance 'sample)))))")
              (list sample) nil (list sample) record-observer :external-callback-representation)
      (reject (read-from-string "((defclass sample () ())
                    (defun external-record-pack () (values (make-instance 'sample)))
                    (defun entry () (multiple-value-call #'record-observer (external-record-pack))))")
              (list sample) nil (list sample) record-observer :external-value-representation)
      (reject (read-from-string "((defclass sample () ())
                                  (defparameter *captured* (list nil))
                                  (defun entry () (setf (car *captured*) (make-instance 'sample))
                                                 (aggregate-observer)))")
              (list sample) nil (list sample) aggregate-observer :external-shared-state-representation)
      (reject (read-from-string "((defclass sample () ())
                                  (defun save (parameter) (declare (special parameter)) (parameter-observer))
                                  (defun entry () (save (make-instance 'sample))))")
              (list sample) nil (list sample) (intern "PARAMETER-OBSERVER" *package*) :external-shared-state-representation)
      (let ((base (read-from-string "((defgeneric value (x)) (defmethod value ((x number)) x))")))
        (reject (append base (read-from-string "((defun entry () (callable-observer #'value)))"))
                nil (list value) '(number) callable-observer :external-value-representation)
        (dolist (body '("(eq #'value (function-observer))"
                        "(eql #'value (function-observer))"
                        "(equal #'value (function-observer))"
                        "(equalp #'value (function-observer))"
                        "(funcall #'eq #'value (function-observer))"
                        "(apply #'eq (list #'value (function-observer)))"
                        "(multiple-value-call #'eq (values #'value) (values (function-observer)))"))
          (reject (append base (list (list 'defun entry nil (read-from-string body))))
                  nil (list value) '(number) (intern "FUNCTION-OBSERVER" *package*) :external-logical-identity))
        (reject (append base (read-from-string
                              "((defun entry () (mapcar #'eq (list #'value) (list (function-observer)))))"))
                nil (list value) '(number) (intern "FUNCTION-OBSERVER" *package*) :external-logical-identity)
        ;; A zero-argument opaque operation reads the actual source symbol;
        ;; no direct argument audit can detect this publication channel.
        (dolist (initializer '("#'value" "(load-time-value #'value)"))
          (reject (append base (list (list 'defparameter captured (read-from-string initializer))
                                    (list 'defun entry nil (list state-observer))))
                  nil (list value) '(number) state-observer :external-shared-state-representation))
        (dolist (body '("(let ((*captured* #'value)) (state-observer))"
                        "(let* ((*captured* #'value)) (state-observer))"
                        "(progn (setq *captured* #'value) (state-observer))"
                        "(progn (setf *captured* #'value) (state-observer))"
                        "(multiple-value-bind (ignored *captured*) (values 0 #'value) (declare (ignore ignored)) (state-observer))"
                        "(multiple-value-bind (ignored *captured*) (producer) (declare (ignore ignored)) (state-observer))"))
          (reject (append base (read-from-string "((defparameter *captured* nil))")
                          (read-from-string "((defun producer () (values 0 #'value)))")
                          (list (list 'defun entry nil (read-from-string body))))
                  nil (list value) '(number) state-observer :external-shared-state-representation))
        (reject (append base (read-from-string "((defparameter *captured* nil)
                            (defun partial-producer () (if (plusp 1) (values #'value 0) (values #'value)))
                            (defun entry () (multiple-value-bind (*captured* ignored) (partial-producer)
                                              (declare (ignore ignored)) (state-observer))))"))
                nil (list value) '(number) state-observer :external-shared-state-representation)
        (reject (append base (read-from-string "((defparameter *captured* nil)
                       (defun variable-state-producer ()
                         (if (plusp 1) (values 0 :tag #'value) (values 0 :tag #'value :extra)))
                       (defun entry () (multiple-value-bind (a b *captured* extra) (variable-state-producer)
                                         (declare (ignore a b extra)) (state-observer))))"))
                nil (list value) '(number) state-observer :external-shared-state-representation)
        ;; Proved native secondary values and ordinary NIL padding remain
        ;; compatible with the unchanged zero-argument external observer.
        (dolist (producer '("(values 0 :tag)" "(values 0)" "(producer)"))
          (let* ((forms (append base (read-from-string "((defparameter *captured* nil))")
                                (read-from-string "((defun producer () (values 0 :tag)))")
                                (list (list 'defun entry nil
                                            (read-from-string
                                             (format nil "(multiple-value-bind (ignored *captured*) ~A (declare (ignore ignored)) (state-observer))" producer))))))
                 (unit (snowgrave:close-source-unit
                        (list :forms forms) :unit-name (list 'native-secondary-shared producer)
                        :closed-generics (list value) :universe '(number)
                        :entries (list entry) :external-domains (list (list entry nil))
                        :external-operations (list state-observer)
                        :external-return-domains (list (list state-observer '(boolean))))))
            (dolist (form forms) (eval form))
            (check (not (funcall entry)))
            (check (not (funcall (snowgrave:unit-function unit entry))))))
        (let* ((forms (append base (read-from-string "((defparameter *captured* nil)
                          (defun partial-producer () (if (plusp 1) (values 0 :tag) (values 0)))
                          (defun entry () (multiple-value-bind (*captured* ignored) (partial-producer)
                                            (declare (ignore ignored)) (state-observer))))")))
               (unit (snowgrave:close-source-unit
                      (list :forms forms) :unit-name '(native-partial-primary-shared)
                      :closed-generics (list value) :universe '(number)
                      :entries (list entry) :external-domains (list (list entry nil))
                      :external-operations (list state-observer)
                      :external-return-domains (list (list state-observer '(boolean))))))
          (dolist (form forms) (eval form))
          (check (not (funcall entry)))
          (check (not (funcall (snowgrave:unit-function unit entry)))))
        (let* ((forms (append base (read-from-string "((defparameter *captured* nil)
                       (defun native-variable-producer ()
                         (if (plusp 1) (values 0 #'value :tag) (values 0 #'value)))
                       (defun entry () (multiple-value-bind (a b *captured*) (native-variable-producer)
                                         (declare (ignore a b)) (state-observer))))")))
               (unit (snowgrave:close-source-unit
                      (list :forms forms) :unit-name '(native-variable-secondary-shared)
                      :closed-generics (list value) :universe '(number)
                      :entries (list entry) :external-domains (list (list entry nil))
                      :external-operations (list state-observer)
                      :external-return-domains (list (list state-observer '(boolean))))))
          (dolist (form forms) (eval form))
          (check (not (funcall entry)))
          (check (not (funcall (snowgrave:unit-function unit entry)))))))))

(defun sequence-result-domain-tests ()
  (let* ((*package* (find-package :snowgrave.sequence-result.fixture))
         (base (read-from-string "((defgeneric only-list (x)) (defmethod only-list ((x list)) (values x :list)))"))
         (generic (intern "ONLY-LIST" *package*)) (entry (intern "ENTRY" *package*)))
    (labels ((close-bad (forms)
               (snowgrave:close-source-unit
                (list :forms forms) :unit-name (list 'false-sequence-domain (third (car (last forms))))
                :universe '(list) :closed-generics (list generic) :entries (list entry)
                :external-domains (list (list entry '(t))))))
      (loop for body in '("(only-list (reverse x))" "(only-list (list* x))" "(only-list (append x))"
                         "(let ((answer (append x))) (only-list answer))" "(only-list (append nil x))")
            for input in (list (vector 1 2) 7 7 7 7)
            for forms = (append base (list (list 'defun entry (list (intern "X" *package*)) (read-from-string body))))
            do (dolist (form forms) (eval form))
               (check (eq (type-of (handler-case (funcall entry input) (error (condition) condition)))
                          (find-symbol "NO-APPLICABLE-METHOD-ERROR" "SB-PCL")))
               (let ((condition (handler-case (close-bad forms) (snowgrave:incomplete-domain (condition) condition))))
                 (check (typep condition 'snowgrave:incomplete-domain))
                 (check (eq (snowgrave:error-feature condition) :internal-call-domain))))
      (let* ((forms (append base (read-from-string
                      "((defun sequence-helper (x) (list* x)) (defun entry (x) (only-list (sequence-helper x))))")))
             (condition (handler-case (close-bad forms) (snowgrave:incomplete-domain (condition) condition))))
        (check (typep condition 'snowgrave:incomplete-domain))
        (check (eq (snowgrave:error-feature condition) :internal-call-domain))))
    (let* ((forms (append base (read-from-string
                    "((defgeneric only-vector (x)) (defmethod only-vector ((x vector)) (values x :vector))
                       (defun list-reverse (x) (only-list (reverse x)))
                       (defun identity-liststar (x) (only-list (list* x)))
                       (defun identity-append (x) (only-list (append x)))
                       (defun liststar-pair (x y) (only-list (list* x y)))
                       (defun append-cons-tail (x y) (only-list (append x y)))
                       (defun append-list-tail (x y) (only-list (append x y)))
                       (defun append-empty () (only-list (append)))
                       (defun vector-reverse (x) (only-vector (reverse x)))
                       (defun string-reverse (x) (only-vector (reverse x))))")))
           (entries (mapcar (lambda (name) (intern name *package*))
                           '("LIST-REVERSE" "IDENTITY-LISTSTAR" "IDENTITY-APPEND" "LISTSTAR-PAIR" "APPEND-CONS-TAIL"
                             "APPEND-LIST-TAIL" "APPEND-EMPTY" "VECTOR-REVERSE" "STRING-REVERSE")))
           (domains '((list) (list) (list) (t t) (cons t) (list list) () (vector) (string)))
           (unit (snowgrave:close-source-unit
                  (list :forms forms) :unit-name '(sequence-result-domains)
                  :universe '(list vector cons string) :closed-generics (list generic (intern "ONLY-VECTOR" *package*))
                  :entries entries :external-domains (mapcar #'list entries domains)))
           (arguments (list (list '(1 2)) (list '(1 2)) (list '(1 2)) '(1 :tail) '((1 2) :tail)
                            '(nil (8 9)) nil (list (vector 1 2)) '("abc"))))
      (dolist (form forms) (eval form))
      (loop for entry in entries for args in arguments
            do (check (equalp (multiple-value-list (apply entry args))
                             (multiple-value-list (apply (snowgrave:unit-function unit entry) args)))))
      (let ((value (list 1 2)))
        (dolist (name '("IDENTITY-LISTSTAR" "IDENTITY-APPEND"))
          (check (eq (funcall (snowgrave:unit-function unit name) value) value)))
        (check (eq (funcall (snowgrave:unit-function unit "APPEND-LIST-TAIL") nil value) value)))
      (let* ((root (asdf:system-source-directory "snowgrave"))
             (source (merge-pathnames ".build/fresh-sequence-results.lisp" root))
             (data (merge-pathnames ".build/fresh-sequence-results.metadata" root)))
        (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
        (with-open-file (stream data :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
        (check (search "Fresh sequence result domains executed."
                 (uiop:run-program
                  (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                        (namestring (merge-pathnames "scripts/fresh-sequence-results.lisp" root))
                        (namestring source) (namestring data)) :output :string)))))))

(defun precedence-tests ()
  (let* ((*package* (find-package :snowgrave.fixture))
         (forms (read-from-string
                 "((defclass precedence-policy () ())
                    (defclass precedence-fast (precedence-policy) ())
                    (defgeneric precedence-pair (p q) (:argument-precedence-order q p))
                    (defmethod precedence-pair ((p precedence-policy) (q precedence-policy)) (list :root))
                    (defmethod precedence-pair ((p precedence-fast) (q precedence-policy)) (cons :first (call-next-method)))
                    (defmethod precedence-pair ((p precedence-policy) (q precedence-fast)) (cons :second (call-next-method)))
                    (defun pair-entry (p q) (precedence-pair p q)))"))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(argument-precedence :version 1)
                :closed-classes (read-from-string "(precedence-policy precedence-fast)")
                :universe (read-from-string "(precedence-policy precedence-fast)")
                :closed-generics (read-from-string "(precedence-pair)")
                :entries (read-from-string "(pair-entry)")
                :external-domains (read-from-string "((pair-entry (precedence-policy precedence-policy)))")))
         (layouts (getf (snowgrave:unit-metadata unit) :record-layouts)))
    (dolist (form forms) (eval form))
    (dolist (left layouts)
      (dolist (right layouts)
        (flet ((record (layout)
                 (snowgrave:sg-make-record
                  (snowgrave:make-layout (getf layout :identity) (getf layout :class)
                                        (getf layout :ancestors) (getf layout :slots)
                                        :error-mapping (getf layout :error-mapping)))))
          (check (equal (funcall (intern "PAIR-ENTRY" *package*)
                                (make-instance (getf left :class)) (make-instance (getf right :class)))
                        (funcall (test-unit-function unit 'pair-entry) (record left) (record right)))))))
    (let ((fast (find (intern "PRECEDENCE-FAST" *package*) layouts :key (lambda (layout) (getf layout :class)))))
      (check (equal (funcall (test-unit-function unit 'pair-entry)
                            (snowgrave:sg-make-record (snowgrave:make-layout (getf fast :identity) (getf fast :class)
                                                                            (getf fast :ancestors) (getf fast :slots)
                                        :error-mapping (getf fast :error-mapping)))
                            (snowgrave:sg-make-record (snowgrave:make-layout (getf fast :identity) (getf fast :class)
                                                                            (getf fast :ancestors) (getf fast :slots)
                                        :error-mapping (getf fast :error-mapping))))
                    '(:second :first :root))))))

(defun argument-contract-forms ()
  (let ((*package* (find-package :snowgrave.fixture)))
    (read-from-string
     "((defclass argument-policy () ())
        (defclass argument-fast (argument-policy) ())
        (defparameter *argument-log* nil)
        (defparameter *argument-around-tail* nil)
        (defun argument-default (tag value) (push tag *argument-log*) value)
        (defgeneric keyword-call (p &optional n &key))
        (defmethod keyword-call :around ((p argument-policy) &optional (n (argument-default :around-opt 11) supplied)
                                        &rest tail &key (around (argument-default :around-key 12) around-p))
          (push (list :around n supplied tail around around-p) *argument-log*)
          (setq *argument-around-tail* tail)
          (call-next-method))
        (defmethod keyword-call :before ((p argument-policy) &optional (n (argument-default :before-opt 21))
                                        &key (before (argument-default :before-key 22)))
          (push (list :before n before) *argument-log*))
        (defmethod keyword-call :after ((p argument-policy) &optional (n (argument-default :after-opt 31))
                                       &key (after (argument-default :after-key 32)))
          (push (list :after n after) *argument-log*))
        (defmethod keyword-call ((p argument-policy) &optional (n (argument-default :base-opt 41) supplied)
                                &rest tail &key ((:named alpha) (argument-default :base-key 42) alpha-p))
          (push (list :primary n supplied alpha alpha-p) *argument-log*)
          (values n supplied alpha alpha-p tail (eq tail *argument-around-tail*)))
        (defmethod keyword-call ((p argument-fast) &optional (n (argument-default :fast-opt 51) supplied)
                                &key (fast (argument-default :fast-key 52)))
          (push (list :fast n supplied fast) *argument-log*)
          (call-next-method))
        (defgeneric bounded-call (p &optional n))
        (defmethod bounded-call ((p argument-policy) &optional (n (argument-default :bounded 61) supplied))
          (values n supplied))
        (defgeneric rest-call (p &rest tail))
        (defmethod rest-call ((p argument-policy) &rest tail &key a) (values tail a))
        (defgeneric allow-call (p &key))
        (defmethod allow-call ((p argument-policy) &key a &allow-other-keys) a)
        (defun keyword-entry (p &rest tail) (apply #'keyword-call p tail))
        (defun bounded-entry (p &rest tail) (apply #'bounded-call p tail))
        (defun rest-entry (p &rest tail) (apply #'rest-call p tail))
        (defun allow-entry (p &rest tail) (apply #'allow-call p tail))
        (defun keyword-function () #'keyword-call)
        (defun ordinary-entry (p &optional (n (argument-default :ordinary-opt 71) supplied)
                              &rest tail &key ((:named alpha) (argument-default :ordinary-key 72) alpha-p)
                              &allow-other-keys &aux (sum (+ n alpha)))
          (values n supplied alpha alpha-p tail sum)))")))

(defun condition-observation (condition logical-bindings)
  (labels ((logical (object)
             (let ((binding (assoc object logical-bindings :test #'eq)))
               (cond (binding (cdr binding))
                     ((consp object) (cons (logical (car object)) (logical (cdr object))))
                     (t object)))))
      (list :condition (type-of condition)
            :slots (loop for slot in (sb-mop:class-slots (class-of condition))
                         for name = (sb-mop:slot-definition-name slot)
                         when (slot-boundp condition name)
                           collect (list name (logical (slot-value condition name)))))))

(defun contract-observation (function arguments &optional logical-bindings)
  (handler-case (list :values (multiple-value-list (apply function arguments)))
    (error (condition) (condition-observation condition logical-bindings))))

(defpackage #:snowgrave.method-initializer.fixture
  (:use #:cl)
  (:shadowing-import-from #:snowgrave #:defclass #:defgeneric #:defmethod))

(defun method-initializer-forms ()
  (read-from-string
   "((defclass base () ()) (defclass leaf (base) ())
      (defparameter *trace* nil)
      (defparameter *seed* 7)
      (defgeneric optional-call (r &optional n))
      (defmethod optional-call ((r base) &optional (n (progn (push :base-default *trace*) 7)))
        (declare (ignore r)) (push :base *trace*) n)
      (defmethod optional-call ((r leaf) &optional
                                (n (progn (push :leaf-default *trace*)
                                          (if (next-method-p) (call-next-method) 13)) supplied))
        (declare (ignore r)) (push :leaf *trace*)
        (values n :optional supplied (reverse *trace*)))
      (defgeneric key-call (r &key value))
      (defmethod key-call ((r base) &key (value (progn (push :base-default *trace*) 19)))
        (declare (ignore r)) (push :base *trace*) value)
      (defmethod key-call ((r leaf) &key
                          (value (progn (push :leaf-default *trace*)
                                        (if (next-method-p) (call-next-method) 23)) supplied))
        (declare (ignore r)) (push :leaf *trace*)
        (values value :key supplied (reverse *trace*)))
      (defgeneric aux-call (r &optional n))
      (defmethod aux-call ((r base) &optional (n (progn (push :base-default *trace*) 5)))
        (declare (ignore r)) (push :base *trace*) n)
      (defmethod aux-call ((r leaf) &optional n
                          &aux (probe (call-next-method)) (has-next (next-method-p)))
        (declare (ignore r)) (push :leaf *trace*)
        (values probe has-next n (reverse *trace*)))
      (defgeneric flet-call (r))
      (defmethod flet-call ((r base)) (declare (ignore r)) (push :base *trace*) 31)
      (defmethod flet-call ((r leaf))
        (declare (ignore r))
        (flet ((local (&optional (n (call-next-method)))
                 (values n (next-method-p) :flet (reverse *trace*))))
          (local)))
      (defgeneric labels-call (r))
      (defmethod labels-call ((r base)) (declare (ignore r)) (push :base *trace*) 37)
      (defmethod labels-call ((r leaf))
        (declare (ignore r))
        (labels ((local (&key (n (if (next-method-p) (call-next-method) 41)))
                   (values n (next-method-p) :labels (reverse *trace*))))
          (local)))
      (defgeneric lambda-call (r))
      (defmethod lambda-call ((r base)) (declare (ignore r)) (push :base *trace*) 47)
      (defmethod lambda-call ((r leaf))
        (declare (ignore r))
        (funcall (lambda (&optional (n (call-next-method)))
                   (values n (next-method-p) :lambda (reverse *trace*)))))
      (defgeneric nested-call (r &optional n))
      (defmethod nested-call ((r base) &optional n)
        (declare (ignore r n)) (push :base *trace*) 61)
      (defmethod nested-call ((r leaf) &optional
                             (n (funcall (lambda (&optional (inner (call-next-method))) inner))))
        (declare (ignore r)) (values n (next-method-p) :nested (reverse *trace*)))
      (defgeneric lone-call (r &optional n))
      (defmethod lone-call ((r base) &optional (n (if (next-method-p) (call-next-method) nil) supplied))
        (declare (ignore r)) (values n (next-method-p) supplied (reverse *trace*)))
      (defgeneric lone-error (r &optional n))
      (defmethod lone-error ((r base) &optional
                            (n (progn (push :default *trace*) (call-next-method))))
        (declare (ignore r)) (push :body *trace*) n)
      (defgeneric special-call (r &optional n))
      (defmethod special-call ((r base) &optional (n (progn (incf *seed*) *seed*)))
        (declare (ignore r)) (values n *seed*))
      (defun boot-leaf () (make-instance 'leaf))
      (defun boot-base () (make-instance 'base))
      (defun optional-entry (r flag n)
        (let ((*trace* nil)) (if flag (optional-call r n) (optional-call r))))
      (defun key-entry (r flag n)
        (let ((*trace* nil)) (if flag (key-call r :value n :value 999) (key-call r))))
      (defun aux-entry (r flag n)
        (let ((*trace* nil)) (if flag (aux-call r n) (aux-call r))))
      (defun lone-entry (r flag n)
        (let ((*trace* nil)) (if flag (lone-call r n) (lone-call r))))
      (defun error-entry (r flag n) (if flag (lone-error r n) (lone-error r)))
      (defun special-entry (r flag n)
        (let ((*seed* 19)) (if flag (special-call r n) (special-call r))))
      (defun unbound-special-entry (r) (special-call r))
      (defun flet-entry (r) (let ((*trace* nil)) (flet-call r)))
      (defun labels-entry (r) (let ((*trace* nil)) (labels-call r)))
      (defun lambda-entry (r) (let ((*trace* nil)) (lambda-call r)))
      (defun nested-entry (r flag n)
        (let ((*trace* nil)) (if flag (nested-call r n) (nested-call r)))))"))

(defun method-initializer-tests ()
  (let* ((*package* (find-package :snowgrave.method-initializer.fixture))
         (identity '(method-initializers :version 1))
         (forms (method-initializer-forms))
         (base (intern "BASE")) (leaf (intern "LEAF"))
         (generics (mapcar #'intern '("OPTIONAL-CALL" "KEY-CALL" "AUX-CALL" "FLET-CALL"
                                     "LABELS-CALL" "LAMBDA-CALL" "NESTED-CALL" "LONE-CALL" "LONE-ERROR" "SPECIAL-CALL")))
         (names '("OPTIONAL-ENTRY" "KEY-ENTRY" "AUX-ENTRY" "FLET-ENTRY" "LABELS-ENTRY"
                  "LAMBDA-ENTRY" "NESTED-ENTRY" "LONE-ENTRY" "ERROR-ENTRY" "SPECIAL-ENTRY"))
         (entries (mapcar #'intern (append names '("BOOT-LEAF" "BOOT-BASE" "UNBOUND-SPECIAL-ENTRY"))))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name identity
                :closed-classes (list base leaf) :universe (list base leaf 'number)
                :closed-generics generics :entries entries
                :external-domains
                (append (loop for name in names
                              collect (list (intern name)
                                            (if (member name '("FLET-ENTRY" "LABELS-ENTRY" "LAMBDA-ENTRY") :test #'equal)
                                                (list leaf)
                                                (list (if (member name '("LONE-ENTRY" "ERROR-ENTRY") :test #'equal) base leaf) t 'number))))
                        (list (list (intern "BOOT-LEAF") nil) (list (intern "BOOT-BASE") nil)
                              (list (intern "UNBOUND-SPECIAL-ENTRY") (list base))))))
         (expected nil))
    (check (eq (getf (snowgrave:unit-report unit) :claim) :semantically-closed))
    (check (= (symbol-value (intern "*SEED*")) 7))
    (dolist (form forms) (eval form))
    (let* ((native-leaf (funcall (intern "BOOT-LEAF")))
           (native-base (funcall (intern "BOOT-BASE")))
           (record-leaf (funcall (test-unit-function unit "BOOT-LEAF")))
           (record-base (funcall (test-unit-function unit "BOOT-BASE"))))
      (dolist (name (remove "ERROR-ENTRY" names :test #'equal))
        (let* ((basep (equal name "LONE-ENTRY"))
               (unaryp (member name '("FLET-ENTRY" "LABELS-ENTRY" "LAMBDA-ENTRY") :test #'equal))
               (cases nil))
          (dolist (tail (if unaryp '(nil) '((nil 83) (t 83))))
            (let ((native (multiple-value-list (apply (intern name) (if basep native-base native-leaf) tail)))
                  (closed (multiple-value-list (apply (test-unit-function unit name) (if basep record-base record-leaf) tail))))
              (check (equal native closed))
              (push (list tail native) cases)))
          (push (list name basep (nreverse cases)) expected)))
      ;; A genuinely absent next method still signals the exact native condition,
      ;; including original arguments and method/generic identity; no body effect.
      (let* ((generic (intern "LONE-ERROR"))
             (native-gf (fdefinition generic))
             (logical-gf (list identity :generic generic))
             (method (find-method native-gf nil (list (find-class base))))
             (logical-method (list identity :method generic nil (list base)))
             (trace (intern "*TRACE*"))
             (native-bindings (list (cons native-base :record) (cons native-gf logical-gf) (cons method logical-method)))
             (closed-bindings (list (cons record-base :record) (cons (test-code-function unit generic) logical-gf))))
        (dolist (tail '((nil 83) (t 83)))
          (let (native closed native-effects closed-effects)
            (progv (list trace) (list nil)
              (setf native (contract-observation (intern "ERROR-ENTRY") (cons native-base tail) native-bindings)
                    native-effects (copy-list (symbol-value trace))))
            (progv (list trace) (list nil)
              (setf closed (contract-observation (test-unit-function unit "ERROR-ENTRY") (cons record-base tail) closed-bindings)
                    closed-effects (copy-list (symbol-value trace))))
            (check (equal native closed))
            (check (equal native-effects closed-effects)))))
      (let ((seed (intern "*SEED*")) (entry (intern "UNBOUND-SPECIAL-ENTRY")))
        (unwind-protect
             (progn (makunbound seed)
                    (check (equal (contract-observation entry (list native-base))
                                  (contract-observation (test-unit-function unit entry) (list record-base)))))
          (setf (symbol-value seed) 7))))
    (let* ((changed-entry (intern "CHANGED-ENTRY"))
           (changed-generic (intern "CHANGED-CALL"))
           (changed (read-from-string
                     "((defclass base () ()) (defclass leaf (base) ())
                        (defgeneric changed-call (r &optional n))
                        (defmethod changed-call ((r base) &optional n) (declare (ignore r)) n)
                        (defmethod changed-call ((r leaf) &optional (n (call-next-method r 9))) n)
                        (defun changed-entry (r) (changed-call r)))"))
           (condition (handler-case
                          (snowgrave:close-source-unit
                           (list :forms changed) :unit-name '(changed-method-initializer)
                           :closed-classes (list base leaf) :universe (list base leaf)
                           :closed-generics (list changed-generic) :entries (list changed-entry)
                           :external-domains (list (list changed-entry (list leaf))))
                        (snowgrave:unsupported-definition (condition) condition))))
      (check (typep condition 'snowgrave:unsupported-definition))
      (check (eq (snowgrave:error-feature condition) :changed-argument-next-method)))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-method-initializers.lisp" root))
           (metadata (merge-pathnames ".build/fresh-method-initializers.metadata" root))
           (observations (merge-pathnames ".build/fresh-method-initializers.expected" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (with-open-file (stream observations :direction :output :if-exists :supersede) (write (nreverse expected) :stream stream :readably t))
      (check (search "Fresh method initializers executed."
                     (uiop:run-program
                      (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                            (namestring (merge-pathnames "scripts/fresh-method-initializers.lisp" root))
                            (namestring source) (namestring metadata) (namestring observations)) :output :string))))))

(defun miss-trace (function arguments logical-bindings retry-once)
  (let ((trace nil) (count 0))
    (handler-case
        (handler-bind ((error (lambda (condition)
                                (let ((retry (find-restart 'sb-ext:retry condition)))
                                  (push (list (condition-observation condition logical-bindings)
                                              (mapcar #'restart-name (compute-restarts condition))
                                              (when retry (princ-to-string retry))) trace)
                                  (incf count)
                                  (when (and retry-once (= count 1)
                                             (typep condition 'sb-pcl::no-applicable-method-error))
                                    (invoke-restart retry))))))
          (apply function arguments))
      (error () (nreverse trace)))))

(defun miss-tests ()
  (let* ((*package* (find-package :snowgrave.fixture))
         (identity '(standard-misses :version 1))
         (forms (read-from-string
                 "((defparameter *miss-log* nil)
                    (defgeneric next-only (x &optional y &key))
                    (defmethod next-only ((x t) &optional (y 10) &key extra)
                      (push (list :call x y extra) *miss-log*)
                      (unwind-protect (call-next-method) (push :cleanup *miss-log*)))
                    (defgeneric miss-only (x))
                    (defmethod miss-only ((x number)) :numeric)
                    (defun next-entry (x &rest tail) (apply #'next-only x tail))
                    (defun miss-entry (x &rest tail) (apply #'miss-only x tail))
                    (defun numeric-entry (x &rest tail) (apply #'miss-only x tail)))"))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name identity :universe '(number symbol)
                :closed-generics (read-from-string "(next-only miss-only)")
                :entries (read-from-string "(next-entry miss-entry numeric-entry)")
                :external-domains (read-from-string "((next-entry (number)) (miss-entry (symbol)) (numeric-entry (number)))")))
         (log (intern "*MISS-LOG*" *package*)))
    (dolist (form forms) (eval form))
    (dolist (entry '("NEXT-ENTRY" "MISS-ENTRY"))
      (let* ((generic (intern (if (string= entry "NEXT-ENTRY") "NEXT-ONLY" "MISS-ONLY") *package*))
             (open-gf (fdefinition generic))
             (closed-gf (test-code-function unit generic))
             (logical-gf (list identity :generic generic))
             (method (when (string= entry "NEXT-ENTRY") (find-method open-gf nil (list (find-class t)))))
             (logical-method (when method (list identity :method generic nil '(t))))
             (open-bindings (append (list (cons open-gf logical-gf)) (when method (list (cons method logical-method)))))
             (closed-bindings (list (cons closed-gf logical-gf))))
        (dolist (warm '(nil t))
         (when (and warm (null method))
           (check (eq (funcall (intern "NUMERIC-ENTRY" *package*) 1) :numeric))
           (check (eq (funcall (test-unit-function unit 'numeric-entry) 1) :numeric)))
         (dolist (arguments (if method '((1) (2 3 :extra 4) (1 2 :unknown 3))
                               '((:outside) (nil) (hello :extra 3))))
          (let (open-trace open-effects closed-trace closed-effects)
            (progv (list log) (list nil)
              (setf open-trace (miss-trace (intern entry *package*) arguments open-bindings (null method))
                    open-effects (copy-tree (symbol-value log))))
            (progv (list log) (list nil)
              (setf closed-trace (miss-trace (test-unit-function unit entry) arguments closed-bindings (null method))
                    closed-effects (copy-tree (symbol-value log))))
            (check (equal open-trace closed-trace))
            (check (equal open-effects closed-effects)))))))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-misses.lisp" root))
           (metadata (merge-pathnames ".build/fresh-misses.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede)
        (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede)
        (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh miss materialization executed."
                     (uiop:run-program (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                                             (namestring (merge-pathnames "scripts/fresh-misses.lisp" root))
                                             (namestring source) (namestring metadata)) :output :string))))))

(defun argument-contract-tests ()
  (let* ((*package* (find-package :snowgrave.fixture))
         (forms (argument-contract-forms))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(argument-contracts :version 1)
                :closed-classes (read-from-string "(argument-policy argument-fast)")
                :universe (read-from-string "(argument-policy argument-fast)")
                :closed-generics (read-from-string "(keyword-call bounded-call rest-call allow-call)")
                :entries (read-from-string "(keyword-entry bounded-entry rest-entry allow-entry ordinary-entry keyword-function)")
                :external-domains (read-from-string "((keyword-entry (argument-policy)) (bounded-entry (argument-policy))
                                                       (rest-entry (argument-policy)) (allow-entry (argument-policy))
                                                       (ordinary-entry (argument-policy)) (keyword-function ()))")))
         (log (intern "*ARGUMENT-LOG*" *package*)))
    (dolist (form forms) (eval form))
    (dolist (layout (getf (snowgrave:unit-metadata unit) :record-layouts))
      (let ((instance (make-instance (getf layout :class)))
            (record (snowgrave:sg-make-record
                     (snowgrave:make-layout (getf layout :identity) (getf layout :class)
                                           (getf layout :ancestors) (getf layout :slots)
                                        :error-mapping (getf layout :error-mapping)))))
        (dolist (entry '("KEYWORD-ENTRY" "BOUNDED-ENTRY" "REST-ENTRY" "ALLOW-ENTRY" "ORDINARY-ENTRY"))
          (dolist (tail '(nil (2) (2 :named 3) (2 :around 4 :before 5 :after 6 :fast 7 :named 8)
                          (2 :named 3 :named 9) (2 :unknown 3) (2 :named)
                          (2 3 4) (2 :unknown 3 :allow-other-keys t)
                          (2 :unknown 3 :allow-other-keys nil :allow-other-keys t)
                          ("outside") (nil :named nil)))
            (let (open-observation open-effects closed-observation closed-effects)
              (progv (list log) (list nil)
                (setf open-observation (contract-observation (intern entry *package*) (cons instance tail))
                      open-effects (copy-tree (symbol-value log))))
              (progv (list log) (list nil)
                (setf closed-observation (contract-observation (test-unit-function unit entry) (cons record tail))
                      closed-effects (copy-tree (symbol-value log))))
              (check (equal open-observation closed-observation))
              (check (equal open-effects closed-effects)))))))
    (labels ((close-case (body)
               (snowgrave:close-source-unit
                (list :forms (replace-entry-body forms "KEYWORD-ENTRY" (read-from-string body)))
                :unit-name (list 'missing-required-contract body)
                :closed-classes (read-from-string "(argument-policy argument-fast)")
                :universe (read-from-string "(argument-policy argument-fast)")
                :closed-generics (read-from-string "(keyword-call bounded-call rest-call allow-call)")
                :entries (read-from-string "(keyword-entry)")
                :external-domains (read-from-string "((keyword-entry (argument-policy)))"))))
      ;; A statically incomplete call has a host arity-error path before
      ;; dispatch. Uncalled ordinary entries do not add caller obligations.
      (let* ((short (close-case "(keyword-call)"))
             (layout (first (getf (snowgrave:unit-metadata short) :record-layouts)))
             (record (snowgrave:sg-make-record
                      (snowgrave:make-layout (getf layout :identity) (getf layout :class)
                                            (getf layout :ancestors) (getf layout :slots)
                                            :error-mapping (getf layout :error-mapping))))
             (entry (intern "KEYWORD-ENTRY")) (generic (intern "KEYWORD-CALL")))
        (dolist (form (replace-entry-body forms "KEYWORD-ENTRY" (read-from-string "(keyword-call)")))
          (eval form))
        (check (equal (contract-observation (fdefinition entry) (list (make-instance (getf layout :class)))
                                           (list (cons (fdefinition generic) :generic)))
                      (contract-observation (test-unit-function short entry) (list record)
                                            (list (cons (test-code-function short generic) :generic))))))
      ;; An unknown APPLY tail can instead supply an unproved required tuple.
      (signals snowgrave:incomplete-domain (close-case "(apply #'keyword-call tail)")))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-contracts.lisp" root))
           (metadata (merge-pathnames ".build/fresh-contracts.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede)
        (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede)
        (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh argument contracts executed."
                     (uiop:run-program (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                                             (namestring (merge-pathnames "scripts/fresh-contracts.lisp" root))
                                             (namestring source) (namestring metadata)) :output :string))))))

(defun custom-miss-rejection-tests ()
  (let ((*package* (find-package :snowgrave.fixture)))
    (dolist (operation '(no-next-method no-applicable-method))
      (let* ((specializers (if (eq operation 'no-next-method)
                               '(standard-generic-function standard-method) '(standard-generic-function)))
             (variables (if (eq operation 'no-next-method) '(g m) '(g)))
             (method nil))
        (unwind-protect
             (progn
               (eval `(cl:defmethod ,operation :before
                        (,@(mapcar #'list variables specializers) &rest arguments)
                        (declare (ignore ,@variables arguments)) nil))
               (setf method (find-method (fdefinition operation) '(:before) (mapcar #'find-class specializers)))
               (signals snowgrave:mop-failure
                 (snowgrave:close-source-unit
                  (list :forms (read-from-string
                                (if (eq operation 'no-next-method)
                                    "((defgeneric rejected-miss (x)) (defmethod rejected-miss ((x t)) (call-next-method)) (defun rejected-entry (x) (rejected-miss x)))"
                                    "((defgeneric rejected-miss (x)) (defmethod rejected-miss ((x number)) :numeric) (defun rejected-entry (x) (rejected-miss x)))")))
                  :unit-name (list 'custom-miss operation) :universe '(number symbol)
                  :closed-generics (read-from-string "(rejected-miss)")
                  :entries (read-from-string "(rejected-entry)")
                  :external-domains (read-from-string "((rejected-entry (number)))"))))
          (when method (remove-method (fdefinition operation) method)))))))

(defun differential-tests ()
  (let* ((forms (fixture-forms))
         (unit (close-fixture '(differential :version 1) forms))
         (package (find-package :snowgrave.fixture))
         (open-run (intern "RUN" package))
         (open-log (intern "*LOG*" package))
         (capture (intern "*CAPTURED*" package))
         (closed-capture (symbol-value capture))
         (last-record nil)
         (closed-log (find "*LOG*" (snowgrave::closed-unit-source unit)
                           :key (lambda (form)
                                  (if (and (consp form) (member (car form) '(defvar defparameter)))
                                      (symbol-name (cadr form)) "")) :test #'string=)))
    (dolist (form forms) (eval form))
    (dolist (class-name '("POLICY" "FAST"))
      (let* ((class-symbol (intern class-name package))
             (description (find class-symbol (getf (snowgrave:unit-metadata unit) :record-layouts)
                                :key (lambda (layout) (getf layout :class))))
             (record (snowgrave:sg-make-record
                      (snowgrave:make-layout (getf description :identity) class-symbol
                                            (getf description :ancestors) (getf description :slots)
                                        :error-mapping (getf description :error-mapping))))
             (instance (make-instance class-symbol)))
        (setf (slot-value instance (intern "VALUE" package)) 3)
        (snowgrave:sg-record-write record (intern "VALUE" package) 3)
        (check (eql (funcall (intern "WRITE-SLOT" package) instance nil)
                    (funcall (test-unit-function unit 'write-slot) record nil)))
        (check (eq (slot-boundp instance (intern "VALUE" package))
                   (funcall (test-unit-function unit 'bound-state) record)))
        (check (eql (funcall (intern "WRITE-SLOT" package) instance 1)
                    (funcall (test-unit-function unit 'write-slot) record 1)))
        (check (eql (funcall (intern "INCREMENT-SLOT" package) instance 2)
                    (funcall (test-unit-function unit 'increment-slot) record 2)))
        (setf last-record record)
        (dolist (number (list 1 (expt 2 70) 1/2 2.5f0 2.5d0 #c(1 2) #c(1f0 2f0) #c(1d0 2d0)))
          (let (open-values open-effects closed-values closed-effects)
            (progv (list open-log) (list nil)
              (setf open-values (multiple-value-list (funcall open-run instance number))
                    open-effects (copy-list (symbol-value open-log))))
            (progv (list open-log capture) (list nil closed-capture)
              (setf closed-values (multiple-value-list (funcall (test-unit-function unit 'run) record number))
                    closed-effects (copy-list (symbol-value (cadr closed-log)))))
            (check (equal open-values closed-values))
            (check (equal open-effects closed-effects))))))
    (sb-mop:set-funcallable-instance-function
     (fdefinition (intern "ACCOUNT" package))
     (lambda (&rest arguments) (declare (ignore arguments)) (error "Open generic poisoned.")))
    ;; An ordinary closed call remains executable after poisoning the original
    ;; generic and both source-world and builder bindings are disjoint.
    (progv (list capture) (list closed-capture)
      (check (equal (multiple-value-list (funcall (test-unit-function unit 'run) last-record 7)) '(10 :tag))))
    (setf (symbol-value capture) closed-capture)
    (check (not (typep (test-unit-function unit 'run) 'generic-function)))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-unit.lisp" root))
           (metadata (merge-pathnames ".build/fresh-unit.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede)
        (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede)
        (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh unit executed."
                     (uiop:run-program (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                                             (namestring (merge-pathnames "scripts/fresh.lisp" root))
                                             (namestring source) (namestring metadata)) :output :string))))))

(defun construction-forms ()
  (let ((*package* (find-package :snowgrave.fixture)))
    (read-from-string
     "((defparameter *construction-log* nil)
        (defun note-init (tag value) (push tag *construction-log*) value)
        (defclass base-record ()
          ((a :initarg :a :initform (note-init :a-base 10) :reader a)
           (b :initarg :b :reader b)
           (untouched))
          (:default-initargs :b (note-init :b-default 20)))
        (defclass child-record (base-record)
          ((a :initarg :x :initform (note-init :a-child 30))
           (c :initform (note-init :c-default 40) :reader c)))
        (defun boot () (make-instance 'child-record :x nil :a 99))
        (defun boot-default () (make-instance 'child-record))
        (defun boot-duplicates () (make-instance 'child-record :a 1 :x 2 :a 3))
        (defun read-state (record)
          (values (a record) (b record) (c record) (slot-boundp record 'untouched)))
        (defun construction-log () (reverse *construction-log*)))")))

(defun close-construction (identity forms)
  (let ((*package* (find-package :snowgrave.fixture)))
    (snowgrave:close-source-unit
     (list :forms forms) :unit-name identity
     :closed-classes (read-from-string "(base-record child-record)")
     :universe (read-from-string "(base-record child-record)")
     :closed-generics (read-from-string "(a b c)")
     :entries (read-from-string "(boot boot-default boot-duplicates read-state construction-log)")
     :external-domains (read-from-string "((boot ()) (boot-default ()) (boot-duplicates ()) (read-state (child-record)) (construction-log ()))"))))

(defun constructor-error-comparison (closer forms identity entry log-name)
  (let* ((*package* (find-package :snowgrave.fixture))
         (unit (funcall closer identity forms))
         (log (intern log-name *package*))
         open-error closed-error open-log closed-log)
    (dolist (form forms) (eval form))
    (progv (list log) (list nil)
      (setf open-error (handler-case (funcall (intern entry *package*)) (error (condition) condition))
            open-log (copy-tree (symbol-value log))))
    (progv (list log) (list nil)
      (setf closed-error (handler-case (funcall (test-unit-function unit entry)) (error (condition) condition))
            closed-log (copy-tree (symbol-value log))))
    (check (typep open-error 'sb-pcl::initarg-error))
    (check (typep closed-error 'sb-pcl::initarg-error))
    (let* ((class (sb-pcl::initarg-error-class open-error))
           (token (sb-pcl::initarg-error-class closed-error))
           (description (find (sb-mop:class-name class) (getf (snowgrave:unit-metadata unit) :record-layouts)
                              :key (lambda (layout) (getf layout :class)))))
      (check (eq token (getf description :class-token)))
      (check (equal (condition-observation open-error (list (cons class :class)))
                    (condition-observation closed-error (list (cons token :class)))))
      (check (equal open-log closed-log)))
    unit))

(defun construction-tests ()
  (let* ((forms (construction-forms))
         (identity (list (copy-seq "construction") :version 1))
         (subclasses (copy-list (sb-mop:class-direct-subclasses (find-class 'standard-object))))
         (unit (close-construction identity forms))
         (package (find-package :snowgrave.fixture))
         (open-log (intern "*CONSTRUCTION-LOG*" package))
         (closed-log (cadr (find "*CONSTRUCTION-LOG*" (snowgrave::closed-unit-source unit)
                                :key (lambda (form) (if (and (consp form) (eq (car form) 'defparameter))
                                                       (symbol-name (cadr form)) "")) :test #'string=))))
    (check (equal subclasses (sb-mop:class-direct-subclasses (find-class 'standard-object))))
    (setf (char (car identity) 0) #\X)
    (check (string= (car (getf (snowgrave:unit-metadata unit) :identity)) "construction"))
    (let ((metadata (snowgrave:unit-metadata unit)))
      (setf (char (car (getf metadata :identity)) 1) #\X)
      (check (string= (car (getf (snowgrave:unit-metadata unit) :identity)) "construction")))
    (dolist (form forms) (eval form))
    (dolist (entry '("BOOT" "BOOT-DEFAULT" "BOOT-DUPLICATES"))
      (let (open-values open-effects closed-values closed-effects)
        (progv (list open-log) (list nil)
          (let ((instance (funcall (intern entry package))))
            (setf open-values (multiple-value-list (funcall (intern "READ-STATE" package) instance))
                  open-effects (copy-list (symbol-value open-log)))))
        (progv (list closed-log) (list nil)
          (let ((record (funcall (test-unit-function unit entry))))
            (setf closed-values (multiple-value-list (funcall (test-unit-function unit 'read-state) record))
                  closed-effects (copy-list (symbol-value closed-log)))))
        (check (equal open-values closed-values))
        (check (equal open-effects closed-effects))))
    (let ((*package* package))
      (constructor-error-comparison
       #'close-construction
       (replace-entry-body forms "BOOT" (read-from-string "(make-instance 'child-record :unknown 7)"))
       '(invalid-standard-initarg :version 1) "BOOT" "*CONSTRUCTION-LOG*"))))


(defun authored-initialization-forms ()
  (let ((*package* (find-package :snowgrave.fixture)))
    (read-from-string
     "((defparameter *authored-init-log* nil)
        (defun init-note (tag value) (push tag *authored-init-log*) value)
        (defclass init-base ()
          ((a :initarg :a :initform (init-note :a-default 10))
           (b :initarg :b :initform (init-note :b-default 20))
           (calibrated) (untouched))
          (:default-initargs :tag (init-note :tag-default :default)))
        (defclass init-child (init-base) ())
        (defmethod initialize-instance :around ((r init-base) &rest args &key skip)
          (init-note :initialize-around-start args)
          (unwind-protect
               (if skip (init-note :initialize-suppressed :ignored) (call-next-method))
            (init-note :initialize-around-cleanup nil)))
        (defmethod initialize-instance :before ((r init-base) &key tag)
          (init-note (list :initialize-before tag) nil)
          (setf (slot-value r 'a) :before-a)
          (setf (slot-value r 'b) :before-b))
        (defmethod initialize-instance ((r init-child) &rest args &key tag)
          (init-note (list :initialize-primary tag) args)
          (multiple-value-prog1 (call-next-method)
            (when (eq tag :fail)
              (error 'simple-error :format-control \"Init failed: ~S\" :format-arguments (list tag)))))
        (defmethod initialize-instance :after ((r init-base) &key tag)
          (setf (slot-value r 'calibrated) tag)
          (init-note :initialize-after nil))
        (defmethod shared-initialize :around ((r init-base) slots &rest args)
          (init-note (list :shared-around-start slots) args)
          (multiple-value-prog1 (call-next-method) (init-note :shared-around-end nil)))
        (defmethod shared-initialize :before ((r init-base) slots &key tag)
          (init-note (list :shared-before slots tag) nil))
        (defmethod shared-initialize :after ((r init-base) slots &key tag)
          (init-note (list :shared-after slots tag) nil))
        (defun authored-boot () (make-instance 'init-child :a nil))
        (defun authored-boot-base () (make-instance 'init-base))
        (defun authored-boot-fail () (make-instance 'init-child :tag :fail))
        (defun authored-boot-allow () (make-instance 'init-child :unknown 99 :allow-other-keys t))
        (defun authored-boot-tag () (make-instance 'init-child :tag :supplied :a 7 :a 8))
        (defun authored-boot-skip () (make-instance 'init-child :skip t))
        (defun authored-state (r)
          (values (slot-boundp r 'a) (if (slot-boundp r 'a) (slot-value r 'a) :unbound)
                  (slot-boundp r 'b) (if (slot-boundp r 'b) (slot-value r 'b) :unbound)
                  (slot-boundp r 'calibrated)
                  (if (slot-boundp r 'calibrated) (slot-value r 'calibrated) :unbound)
                  (slot-boundp r 'untouched)))
        (defun authored-shared (r)
          (slot-makunbound r 'a)
          (shared-initialize r '(a) :tag :reinit)
          r))")))

(defun close-authored-initialization (identity forms)
  (let ((*package* (find-package :snowgrave.fixture)))
    (snowgrave:close-source-unit
     (list :forms forms) :unit-name identity
     :closed-classes (read-from-string "(init-base init-child)")
     :universe (read-from-string "(init-base init-child)")
     :closed-generics '(initialize-instance shared-initialize)
     :entries (read-from-string "(authored-boot authored-boot-base authored-boot-fail authored-boot-allow authored-boot-tag authored-boot-skip authored-state authored-shared)")
     :external-domains (read-from-string "((authored-boot ()) (authored-boot-base ()) (authored-boot-fail ()) (authored-boot-allow ()) (authored-boot-tag ()) (authored-boot-skip ()) (authored-state (init-base)) (authored-shared (init-base)))"))))

(defun authored-initialization-tests ()
  (let* ((*package* (find-package :snowgrave.fixture))
         (forms (authored-initialization-forms))
         (methods (mapcar (lambda (operation) (copy-list (sb-mop:generic-function-methods (fdefinition operation))))
                          '(initialize-instance shared-initialize)))
         (unit (close-authored-initialization '(authored-initialization :version 1) forms))
         (log (intern "*AUTHORED-INIT-LOG*" *package*)))
    (loop for operation in '(initialize-instance shared-initialize) for before in methods
          do (check (equal before (sb-mop:generic-function-methods (fdefinition operation)))))
    (dolist (form forms) (eval form))
    (dolist (entry '(authored-boot authored-boot-base authored-boot-allow authored-boot-tag authored-boot-skip))
      (let (open-state closed-state open-log closed-log)
        (progv (list log) (list nil)
          (let ((instance (funcall (intern (symbol-name entry) *package*))))
            (setf open-state (multiple-value-list (funcall (intern "AUTHORED-STATE" *package*) instance))
                  open-log (copy-tree (symbol-value log)))))
        (progv (list log) (list nil)
          (let ((record (funcall (test-unit-function unit entry))))
            (setf closed-state (multiple-value-list (funcall (test-unit-function unit 'authored-state) record))
                  closed-log (copy-tree (symbol-value log)))))
        (check (equal open-state closed-state))
        (check (equal open-log closed-log))))
    (let ((instance (funcall (intern "AUTHORED-BOOT" *package*)))
          (record (funcall (test-unit-function unit 'authored-boot)))
          open-state closed-state open-log closed-log)
      (progv (list log) (list nil)
        (check (eq instance (funcall (intern "AUTHORED-SHARED" *package*) instance)))
        (setf open-state (multiple-value-list (funcall (intern "AUTHORED-STATE" *package*) instance))
              open-log (copy-tree (symbol-value log))))
      (progv (list log) (list nil)
        (check (eq record (funcall (test-unit-function unit 'authored-shared) record)))
        (setf closed-state (multiple-value-list (funcall (test-unit-function unit 'authored-state) record))
              closed-log (copy-tree (symbol-value log))))
      (check (equal open-state closed-state))
      (check (equal open-log closed-log)))
    (let (open-error closed-error open-log closed-log)
      (progv (list log) (list nil)
        (setf open-error (contract-observation (fdefinition (intern "AUTHORED-BOOT-FAIL" *package*)) nil)
              open-log (copy-tree (symbol-value log))))
      (progv (list log) (list nil)
        (setf closed-error (contract-observation (test-unit-function unit 'authored-boot-fail) nil)
              closed-log (copy-tree (symbol-value log))))
      (check (equal open-error closed-error))
      (check (equal open-log closed-log)))
    (dolist (body '("(shared-initialize r r)"
                    "(shared-initialize r t :tag)"
                    "(apply #'shared-initialize r t (list :tag :ok :extra))"
                    "(apply #'shared-initialize r t (reverse (list :tag :ok)))"))
      (let ((before (mapcar (lambda (operation) (copy-list (sb-mop:generic-function-methods (fdefinition operation))))
                           '(initialize-instance shared-initialize))))
        (signals snowgrave:snowgrave-error
          (close-authored-initialization (list 'bad-authored-initialization body)
                                         (replace-entry-body forms "AUTHORED-SHARED" (read-from-string body))))
        (loop for operation in '(initialize-instance shared-initialize) for methods in before
              do (check (equal methods (sb-mop:generic-function-methods (fdefinition operation)))))))
    (constructor-error-comparison
     #'close-authored-initialization
     (replace-entry-body forms "AUTHORED-BOOT" (read-from-string "(make-instance 'init-child :unknown 7)"))
     '(invalid-authored-initarg) "AUTHORED-BOOT" "*AUTHORED-INIT-LOG*")
    (constructor-error-comparison
     #'close-authored-initialization
     (replace-entry-body forms "AUTHORED-BOOT" (read-from-string "(make-instance 'init-child :unknown 7 :allow-other-keys nil :allow-other-keys t)"))
     '(invalid-authored-allow-first) "AUTHORED-BOOT" "*AUTHORED-INIT-LOG*")
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-initialization.lisp" root))
           (metadata (merge-pathnames ".build/fresh-initialization.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede)
        (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede)
        (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh authored initialization executed."
                     (uiop:run-program (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                                             (namestring (merge-pathnames "scripts/fresh-initialization.lisp" root))
                                             (namestring source) (namestring metadata))
                                       :output :string :error-output :string))))))

(defun initialization-host-rejection-tests ()
  (let ((*package* (find-package :snowgrave.fixture)))
    (dolist (definition '("(cl:defmethod initialize-instance :before ((r standard-object) &rest args) (declare (ignore r args)))"
                          "(cl:defmethod make-instance :before ((class symbol) &rest args) (declare (ignore class args)))"))
      (let* ((form (read-from-string definition))
             (operation (cadr form))
             (before (copy-list (sb-mop:generic-function-methods (fdefinition operation))))
             (method (eval form)))
        (unwind-protect
             (signals snowgrave:unclosed-class-operation
               (close-authored-initialization (list 'extended-host-construction definition)
                                              (authored-initialization-forms)))
          (remove-method (fdefinition operation) method))
        (check (equal before (sb-mop:generic-function-methods (fdefinition operation))))))))

(defun minimum-arity-forms ()
  (let ((*package* (find-package :snowgrave.fixture))
        (forms (list (read-from-string "(defparameter *minimum-log* nil)"))))
    (dolist (spec '(("MIN-FIXED" "" "")
                    ("MIN-OPTIONAL" "&optional c" "&optional (c 17)")
                    ("MIN-REST" "&rest tail" "&rest tail")
                    ("MIN-KEY" "&key k" "&key k")))
      (destructuring-bind (name generic-tail method-tail) spec
        (setf forms
              (append forms
                      (read-from-string
                       (format nil
                               "((defgeneric ~A (a b ~A))
                                  (defmethod ~A ((a number) (b number) ~A)
                                    (push :entered *minimum-log*) (values a b))
                                  (defun ~A-ZERO () (funcall #'~A))
                                  (defun ~A-ONE (x) (funcall #'~A x))
                                  (defun ~A-ENTRY (a b &rest tail) (apply #'~A a b tail))
                                  (defun ~A-MISS (a b) (~A a b))
                                  (defun ~A-FUNCTION () #'~A))"
                               name generic-tail name method-tail name name name name
                               name name name name name name))))))
    forms))

(defun close-minimum-arity (forms)
  (let ((*package* (find-package :snowgrave.fixture)))
    (snowgrave:close-source-unit
     (list :forms forms) :unit-name '(minimum-arity :version 1)
     :closed-classes nil :universe '(number symbol)
     :closed-generics (read-from-string "(min-fixed min-optional min-rest min-key)")
     :entries (loop for form in forms when (eq (car form) 'defun) collect (cadr form))
     :external-domains
     (loop for form in forms when (eq (car form) 'defun)
           collect (list (cadr form) (cond ((search "-ONE" (symbol-name (cadr form))) '(t))
                                          ((search "-ENTRY" (symbol-name (cadr form))) '(number number))
                                          ((search "-MISS" (symbol-name (cadr form))) '(symbol number))
                                          (t nil)))))))

(defun minimum-arity-tests ()
  (let* ((*package* (find-package :snowgrave.fixture))
         (forms (minimum-arity-forms))
         (unit (close-minimum-arity forms))
         (log (intern "*MINIMUM-LOG*" *package*)))
    (dolist (form forms) (eval form))
    (dolist (name '("MIN-FIXED" "MIN-OPTIONAL" "MIN-REST" "MIN-KEY"))
      (let* ((open (fdefinition (intern name *package*)))
             (closed (funcall (test-unit-function unit (concatenate 'string name "-FUNCTION"))))
             (open-binding (list (cons open :generic)))
             (closed-binding (list (cons closed :generic))))
        (dolist (arguments '(nil (1) (:outside)))
          (check (equal (contract-observation open arguments open-binding)
                        (contract-observation closed arguments closed-binding))))
        ;; Static incomplete calls use the same path before any tuple exists.
        (check (equal (contract-observation (fdefinition (intern (concatenate 'string name "-ZERO") *package*)) nil open-binding)
                      (contract-observation (test-unit-function unit (concatenate 'string name "-ZERO")) nil closed-binding)))
        (check (equal (contract-observation (fdefinition (intern (concatenate 'string name "-ONE") *package*)) '(:outside) open-binding)
                      (contract-observation (test-unit-function unit (concatenate 'string name "-ONE")) '(:outside) closed-binding)))
        ;; A miss leaves the initial discriminator's minimum-arity payload.
        (check (equal (contract-observation open '(:outside 2) open-binding)
                      (contract-observation closed '(:outside 2) closed-binding)))
        (check (equal (contract-observation open nil open-binding)
                      (contract-observation closed nil closed-binding)))
        ;; Establish through an applicable call, including argument errors.
        (let ((arguments (cond ((string= name "MIN-FIXED") '(1 2 3))
                               ((string= name "MIN-OPTIONAL") '(1 2 3 4))
                               ((string= name "MIN-KEY") '(1 2 :k))
                               (t '(1 2)))))
          (check (equal (contract-observation open arguments open-binding)
                        (contract-observation closed arguments closed-binding))))
        (dolist (arguments '(nil (1) (:outside)))
          (check (equal (contract-observation open arguments open-binding)
                        (contract-observation closed arguments closed-binding))))
        (let (open-values closed-values open-log closed-log)
          (progv (list log) (list nil)
            (setf open-values (contract-observation open '(1 2) open-binding)
                  open-log (copy-list (symbol-value log))))
          (progv (list log) (list nil)
            (setf closed-values (contract-observation closed '(1 2) closed-binding)
                  closed-log (copy-list (symbol-value log))))
          (check (equal open-values closed-values))
          (check (equal open-log closed-log)))))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-minimum.lisp" root))
           (metadata (merge-pathnames ".build/fresh-minimum.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede)
        (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede)
        (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh minimum arity executed."
                     (uiop:run-program (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                                             (namestring (merge-pathnames "scripts/fresh-minimum.lisp" root))
                                             (namestring source) (namestring metadata)) :output :string))))))

(defun constructor-error-tests ()
  (let ((*package* (find-package :snowgrave.fixture)))
    (dolist (body '("(make-instance 'child-record :unknown 1 :other 2 :unknown 3)"
                    "(make-instance 'child-record :unknown 1 :allow-other-keys nil)"
                    "(make-instance 'child-record :unknown (note-init :unknown-value 7) :allow-other-keys (note-init :allow-value nil))"))
      (constructor-error-comparison #'close-construction
                                    (replace-entry-body (construction-forms) "BOOT" (read-from-string body))
                                    (list 'invalid-constructor body) "BOOT" "*CONSTRUCTION-LOG*"))
    (let* ((forms (replace-entry-body (construction-forms) "BOOT"
                                     (read-from-string "(make-instance 'child-record :unknown (note-init :unknown-value 7) :allow-other-keys (note-init :allow-value t))")))
           (unit (close-construction '(dynamic-allow-other-keys) forms))
           (log (intern "*CONSTRUCTION-LOG*" *package*))
           open-values closed-values open-log closed-log)
      (dolist (form forms) (eval form))
      (progv (list log) (list nil)
        (setf open-values (multiple-value-list (funcall (intern "READ-STATE" *package*) (funcall (intern "BOOT" *package*))))
              open-log (copy-list (symbol-value log))))
      (progv (list log) (list nil)
        (setf closed-values (multiple-value-list (funcall (test-unit-function unit 'read-state) (funcall (test-unit-function unit 'boot))))
              closed-log (copy-list (symbol-value log))))
      (check (equal open-values closed-values))
      (check (equal open-log closed-log)))
    (let* ((forms (construction-forms))
           (class (find (intern "BASE-RECORD" *package*) forms :key #'cadr)))
      (setf (cdr (last (car (last class)))) (read-from-string "(:bad-default (note-init :bad-default 17))"))
      (constructor-error-comparison #'close-construction forms '(invalid-default-initarg) "BOOT" "*CONSTRUCTION-LOG*"))
    (let* ((unit (constructor-error-comparison
                  #'close-construction
                  (replace-entry-body (construction-forms) "BOOT" (read-from-string "(make-instance 'child-record :unknown 7)"))
                  '(fresh-constructor-error) "BOOT" "*CONSTRUCTION-LOG*"))
           (root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-constructor-errors.lisp" root))
           (metadata (merge-pathnames ".build/fresh-constructor-errors.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede)
        (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede)
        (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh constructor errors executed."
                     (uiop:run-program (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                                             (namestring (merge-pathnames "scripts/fresh-constructor-errors.lisp" root))
                                             (namestring source) (namestring metadata)) :output :string))))))

(defun stable-identity-tests ()
  (signals snowgrave:nonreproducible-source (close-fixture (list (make-symbol "UNIT-KEY"))))
  (signals error (snowgrave:make-layout (list (make-symbol "KEY")) 'record '(record) nil))
  (let ((*package* (find-package :snowgrave.fixture)))
    (dolist (method '("(defmethod slot-unbound (class (object policy) slot-name) (declare (ignore class object slot-name)) 99)"
                      "(defmethod no-applicable-method ((generic standard-generic-function) &rest args) (declare (ignore generic args)) :custom)"))
      (signals snowgrave:unclosed-class-operation
        (close-fixture (list 'unclosed-native-protocol method)
                       (append (fixture-forms) (list (read-from-string method)))))))
  (let ((key (list :unit)))
    (setf (cdr key) key)
    (signals error (snowgrave:make-layout key 'record '(record) nil)))
  (let* ((*package* (find-package :snowgrave.fixture))
         (variable (make-symbol "LEXICAL-TEMP"))
         (body (list 'let (list (list variable (intern "N" *package*))) (list '+ variable 1)))
         (unit (close-fixture '(lexical-gensym-source :version 1)
                              (replace-entry-body (fixture-forms) "RUN" body)))
         (root (asdf:system-source-directory "snowgrave"))
         (source (merge-pathnames ".build/fresh-lexical.lisp" root))
         (metadata (merge-pathnames ".build/fresh-lexical.metadata" root)))
    (with-open-file (stream source :direction :output :if-exists :supersede)
      (snowgrave:write-unit-source unit stream))
    (with-open-file (stream metadata :direction :output :if-exists :supersede)
      (snowgrave:write-unit-metadata unit stream))
    (check (search "Fresh lexical symbol sharing executed."
                   (uiop:run-program (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                                           (namestring (merge-pathnames "scripts/fresh-lexical.lisp" root))
                                           (namestring source) (namestring metadata)) :output :string)))))

(defun slot-error-forms ()
  (let ((*package* (find-package :snowgrave.fixture)))
    (read-from-string
     "((defclass slot-policy () ((payload :initarg :payload)))
        (defclass slot-child (slot-policy) ((extra :initarg :extra)))
        (defparameter *slot-log* nil)
        (defun read-absent (p) (slot-value (progn (push :receiver *slot-log*) p) 'absent))
        (defun write-absent (p n)
          (setf (slot-value (progn (push :receiver *slot-log*) p) 'absent)
                (progn (push :value *slot-log*) n)))
        (defun bound-absent (p) (slot-boundp (progn (push :receiver *slot-log*) p) 'absent))
        (defun unbind-absent (p) (slot-makunbound (progn (push :receiver *slot-log*) p) 'absent))
        (defun read-extra (p) (slot-value p 'extra))
        (defun read-hint (p) (slot-value p 'snowgrave.tests::payload))
        (defun read-unbound (p) (slot-value p 'payload)))")))

(defun close-slot-errors (identity &optional (forms (slot-error-forms)))
  (let ((*package* (find-package :snowgrave.fixture)))
    (snowgrave:close-source-unit
     (list :forms forms) :unit-name identity
     :closed-classes (read-from-string "(slot-policy slot-child)")
     :universe (read-from-string "(slot-policy slot-child number)")
     :entries (read-from-string "(read-absent write-absent bound-absent unbind-absent read-extra read-hint read-unbound)")
     :external-domains (read-from-string "((read-absent (slot-policy)) (write-absent (slot-policy number)) (bound-absent (slot-policy)) (unbind-absent (slot-policy)) (read-extra (slot-policy)) (read-hint (slot-policy)) (read-unbound (slot-policy)))"))))

(defun slot-restart-observation (function record logical restart interactive)
  (let ((observation nil)
        (*query-io* (make-two-way-stream (make-string-input-stream "(+ 40 2)")
                                       (make-string-output-stream))))
    (list :values
          (multiple-value-list
           (handler-bind ((unbound-slot
                            (lambda (condition)
                              (setf observation
                                    (list (condition-observation condition (list (cons record logical)))
                                          (mapcar (lambda (name)
                                                    (let ((restart (find-restart name condition)))
                                                      (list name (princ-to-string restart))))
                                                  '(use-value store-value))))
                              (if interactive
                                  (invoke-restart-interactively (find-restart restart condition))
                                  (invoke-restart (find-restart restart condition) 42)))))
             (funcall function record)))
          :condition observation
          :prompt (get-output-stream-string (two-way-stream-output-stream *query-io*)))))

(defun slot-error-tests ()
  (let* ((*package* (find-package :snowgrave.fixture))
         (forms (slot-error-forms))
         (unit (close-slot-errors '(slot-errors :version 1) forms))
         (layouts (getf (snowgrave:unit-metadata unit) :record-layouts))
         (log (intern "*SLOT-LOG*" *package*)))
    (dolist (form forms) (eval form))
    (dolist (description layouts)
      (let* ((class (getf description :class))
             (mapping (getf description :error-mapping))
             (layout (snowgrave:make-layout (getf description :identity) class
                                            (getf description :ancestors) (getf description :slots)
                                            :error-mapping mapping))
             (record (snowgrave:sg-make-record layout))
             (open (make-instance class)))
        (check (snowgrave:sg-record-layout-p record (getf description :identity) class
                                             (getf description :ancestors) (getf description :slots)
                                             :error-mapping mapping))
        (let ((changed (snowgrave::immutable-copy mapping)))
          (setf (getf changed :host-version) "foreign")
          (signals error (snowgrave:make-layout (getf description :identity) class
                                               (getf description :ancestors) (getf description :slots)
                                               :error-mapping changed))
          (check (not (snowgrave:sg-record-layout-p record (getf description :identity) class
                                                   (getf description :ancestors) (getf description :slots)
                                                   :error-mapping changed))))
        (let* ((private-control (getf mapping :missing-control))
               (expected (copy-seq private-control)))
          (setf (char private-control 0) #\!)
          (let ((condition (handler-case (snowgrave:sg-record-read record :absent)
                             (error (condition) condition))))
            (check (equal expected (simple-condition-format-control condition))))
          (setf (char private-control 0) (char expected 0)))
        (dolist (entry '(read-absent write-absent bound-absent unbind-absent read-hint))
          (let ((open-observation nil) (closed-observation nil) (open-log nil) (closed-log nil)
                (tail (when (eq entry 'write-absent) '(17))))
            (progv (list log) (list nil)
              (setf open-observation (contract-observation (intern (symbol-name entry) *package*)
                                                          (cons open tail) (list (cons open :record)))
                    open-log (reverse (symbol-value log))))
            (progv (list log) (list nil)
              (setf closed-observation (contract-observation (test-unit-function unit entry)
                                                            (cons record tail) (list (cons record :record)))
                    closed-log (reverse (symbol-value log))))
            (check (eq (getf open-observation :condition) 'sb-pcl::missing-slot))
            (check (equal open-observation closed-observation))
            (check (equal open-log closed-log))))
        ;; One finite source operation is missing on the base and succeeds on
        ;; the subclass. Neither branch falls back to native object access.
        (when (member (intern "EXTRA" *package*) (getf description :slots))
          (setf (slot-value open (intern "EXTRA" *package*)) nil)
          (snowgrave:sg-record-write record (intern "EXTRA" *package*) nil))
        (check (equal (contract-observation (intern "READ-EXTRA" *package*) (list open) (list (cons open :record)))
                      (contract-observation (test-unit-function unit 'read-extra) (list record) (list (cons record :record)))))
        ;; Raw ABI errors must have the same mapping as source slot wrappers.
        (dolist (operation '(slot-value slot-boundp slot-makunbound))
          (let ((primitive (ecase operation (slot-value #'snowgrave:sg-record-read)
                                  (slot-boundp #'snowgrave:sg-record-boundp)
                                  (slot-makunbound #'snowgrave:sg-record-unbind))))
            (check (equal (contract-observation operation (list open (intern "ABSENT" *package*)) (list (cons open :record)))
                          (contract-observation primitive (list record (intern "ABSENT" *package*)) (list (cons record :record)))))))
        (check (equal (contract-observation (lambda (object) (setf (slot-value object (intern "ABSENT" *package*)) '(a 17)))
                                           (list open) (list (cons open :record)))
                      (contract-observation (lambda (object) (snowgrave:sg-record-write object (intern "ABSENT" *package*) '(a 17)))
                                           (list record) (list (cons record :record)))))
        (signals snowgrave:domain-violation (snowgrave:sg-record-write record (intern "ABSENT" *package*) (list record)))
        (dolist (restart '(use-value store-value))
          (dolist (interactive '(nil t))
            (slot-makunbound open (intern "PAYLOAD" *package*))
            (snowgrave:sg-record-unbind record (intern "PAYLOAD" *package*))
            (check (equal (slot-restart-observation (intern "READ-UNBOUND" *package*) open :record restart interactive)
                          (slot-restart-observation (test-unit-function unit 'read-unbound) record :record restart interactive)))
            (check (eql (slot-boundp open (intern "PAYLOAD" *package*))
                        (snowgrave:sg-record-boundp record (intern "PAYLOAD" *package*))))))))
    (signals snowgrave:unclosed-class-operation
      (close-slot-errors '(unproved-missing-writer)
                         (replace-entry-body forms "WRITE-ABSENT" (read-from-string "(setf (slot-value p 'absent) (list p))"))))
    (signals snowgrave:unclosed-class-operation
      (close-slot-errors '(mutable-special-receiver-effects)
                         (append (replace-entry-body forms "READ-ABSENT"
                                                     (read-from-string "(slot-value (progn (setq p :foreign) p) 'absent)"))
                                 (list (read-from-string "(defparameter p nil)")))))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-slot-errors.lisp" root))
           (metadata (merge-pathnames ".build/fresh-slot-errors.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh slot error mappings executed."
                     (uiop:run-program (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                                             (namestring (merge-pathnames "scripts/fresh-slot-errors.lisp" root))
                                             (namestring source) (namestring metadata)) :output :string))))))

(defun slot-protocol-rejection-tests ()
  (dolist (operation '(slot-missing slot-unbound))
    (let ((method nil))
      (unwind-protect
           (progn
             (eval (if (eq operation 'slot-missing)
                       '(cl:defmethod slot-missing :before ((class standard-class) (object standard-object) slot operation &optional value)
                          (declare (ignore class object slot operation value)) nil)
                       '(cl:defmethod slot-unbound :before ((class standard-class) (object standard-object) slot)
                          (declare (ignore class object slot)) nil)))
             (setf method (find-method (fdefinition operation) '(:before)
                                      (append (list (find-class 'standard-class) (find-class 'standard-object) (find-class t))
                                              (when (eq operation 'slot-missing) (list (find-class t))))))
             (signals snowgrave:unclosed-class-operation
               (close-slot-errors (list 'custom-slot-protocol operation))))
        (when method (remove-method (fdefinition operation) method)))))
  (let ((method nil))
    (unwind-protect
         (progn
           (eval '(cl:defmethod slot-missing :before ((class standard-class) (object standard-object)
                                                      (slot (eql :only-one-slot)) operation &optional value)
                    (declare (ignore class object slot operation value)) nil))
           (setf method (find-method #'slot-missing '(:before)
                                    (list (find-class 'standard-class) (find-class 'standard-object)
                                          (sb-mop:intern-eql-specializer :only-one-slot) (find-class t))))
           (signals snowgrave:unclosed-class-operation (close-slot-errors '(eql-slot-protocol))))
      (when method (remove-method #'slot-missing method))))
  (let ((original (fdefinition 'sb-int:read-evaluated-form)))
    (unwind-protect
         (progn
           (sb-ext:without-package-locks
             (setf (fdefinition 'sb-int:read-evaluated-form) (lambda () '(99))))
           (signals snowgrave:unclosed-class-operation (close-slot-errors '(replaced-slot-restart-reader))))
      (sb-ext:without-package-locks
        (setf (fdefinition 'sb-int:read-evaluated-form) original)))))

(defun function-flow-forms ()
  (let ((*package* (find-package :snowgrave.fixture)))
    (read-from-string
     "((defclass flow-base () ((payload :initarg :payload)))
        (defclass flow-left (flow-base) ())
        (defclass flow-right (flow-base) ())
        (defparameter *flow-log* nil)
        (defgeneric flow-value (p n))
        (defmethod flow-value :before ((p flow-base) (n number)) (flow-note :before n))
        (defmethod flow-value ((p flow-base) (n number))
          (values (+ n (flow-method-read p)) :flow))
        (defmethod flow-value ((p flow-left) (n number))
          (flow-note :left n) (call-next-method))
        (defun flow-note (tag value) (push (list tag value) *flow-log*) value)
        (defun flow-method-read (p) (slot-value p 'payload))
        (defun flow-slot-read (p) (slot-value p 'payload))
        (defun flow-store (p) (slot-value p 'payload))
        (defun (setf flow-store) (value p) (setf (slot-value p 'payload) value))
        (defun flow-leaf (p n) (flow-value p n))
        (defun flow-bridge (p n) (flow-leaf p n))
        (defun flow-cycle-a (p n)
          (if (zerop n) (flow-leaf p 0) (flow-cycle-b p (1- n))))
        (defun flow-cycle-b (p n)
          (if (zerop n) (flow-leaf p 0) (flow-cycle-a p (1- n))))
        (defun flow-optional (p n &optional (bonus (flow-note :bonus 5)) &rest tail &key (tag :default))
          (values (flow-leaf p n) bonus tail tag))
        (defun flow-entry-left (p n)
          (values (flow-bridge p n) (flow-slot-read p) (flow-cycle-a p 3)))
        (defun flow-entry-right (p n)
          (values (flow-bridge p n) (flow-slot-read p) (flow-cycle-b p 4)))
        (defun flow-funcall-entry (p n) (funcall #'flow-bridge p n))
        (defun flow-apply-entry (p n) (apply #'flow-bridge (list p n)))
        (defun flow-optional-entry (p n) (flow-optional p n))
        (defun flow-store-entry (p n) (setf (flow-store p) n))
        (defun flow-increment-entry (p n) (incf (flow-store p) n))
        (defun flow-log-entry () (reverse *flow-log*)))")))

(defun close-function-flow (identity &optional (forms (function-flow-forms)))
  (let ((*package* (find-package :snowgrave.fixture)))
    (snowgrave:close-source-unit
     (list :forms forms) :unit-name identity
     :closed-classes (read-from-string "(flow-base flow-left flow-right)")
     :universe (read-from-string "(flow-base flow-left flow-right number)")
     :closed-generics (read-from-string "(flow-value)")
     :entries (read-from-string "(flow-entry-left flow-entry-right flow-funcall-entry flow-apply-entry flow-optional-entry flow-store-entry flow-increment-entry flow-log-entry)")
     :external-domains (read-from-string
                        "((flow-entry-left (flow-left number)) (flow-entry-right (flow-right number))
                          (flow-funcall-entry (flow-left number)) (flow-apply-entry (flow-left number))
                          (flow-optional-entry (flow-left number)) (flow-store-entry (flow-left number))
                          (flow-increment-entry (flow-left number)) (flow-log-entry ()))"))))

(defun function-flow-tests ()
  (let* ((*package* (find-package :snowgrave.fixture))
         (forms (function-flow-forms))
         (unit (close-function-flow '(function-flow :version 1) forms))
         (log (intern "*FLOW-LOG*" *package*))
         (payload (intern "PAYLOAD" *package*))
         (evidence (getf (snowgrave:unit-report unit) :ordinary-function-flow))
         (slot-proof (find "FLOW-SLOT-READ" (getf evidence :functions)
                           :key #'proof-name :test #'equal))
         (cycle-proof (find "FLOW-CYCLE-A" (getf evidence :functions)
                            :key #'proof-name :test #'equal)))
    (check (eq (getf evidence :method) :finite-argument-binding-fixed-point))
    (check (equal evidence (getf (snowgrave:unit-metadata unit) :ordinary-function-flow)))
    (check (> (getf evidence :iterations) 1))
    (check (equal (car (getf slot-proof :required-domains)) (read-from-string "(or flow-left flow-right)")))
    (check (eq (second (getf cycle-proof :required-domains)) 'number))
    (dolist (form forms) (eval form))
    (dolist (description (remove (intern "FLOW-BASE" *package*)
                                (getf (snowgrave:unit-metadata unit) :record-layouts)
                                :key (lambda (layout) (getf layout :class))))
      (let* ((class (getf description :class))
             (native (make-instance class :payload 17))
             (record (snowgrave:sg-make-record
                      (snowgrave:make-layout (getf description :identity) class
                                            (getf description :ancestors) (getf description :slots)
                                            :error-mapping (getf description :error-mapping))))
             (entries (if (string= (symbol-name class) "FLOW-LEFT")
                          '("FLOW-ENTRY-LEFT" "FLOW-FUNCALL-ENTRY" "FLOW-APPLY-ENTRY" "FLOW-OPTIONAL-ENTRY" "FLOW-STORE-ENTRY" "FLOW-INCREMENT-ENTRY")
                          '("FLOW-ENTRY-RIGHT"))))
        (snowgrave:sg-record-write record payload 17)
        (dolist (entry entries)
          (dolist (number '(0 3 -2 1/2))
            (let (native-values native-log)
              (progv (list log) (list nil)
                (setf native-values (multiple-value-list (funcall (intern entry *package*) native number))
                      native-log (reverse (symbol-value log))))
              (progv (list log) (list nil)
                (check (equal native-values (multiple-value-list (funcall (test-unit-function unit entry) record number))))
                (check (equal native-log (reverse (symbol-value log))))))))))
    (dolist (body '("(progn (flow-bridge p n) #'flow-bridge)"
                    "(let ((f #'flow-bridge)) (funcall f p n))"
                    "(flow-entry-right p n)"
                    "(flow-bridge p 'outside)"))
      (signals snowgrave:incomplete-domain
        (close-function-flow (list 'bad-function-flow body)
                             (replace-entry-body forms "FLOW-ENTRY-LEFT" (read-from-string body)))))
    (signals snowgrave:unclosed-class-operation
      (close-function-flow '(bad-function-setf-flow)
                           (replace-entry-body forms "FLOW-STORE-ENTRY"
                                               (read-from-string "(setf (flow-store :foreign) n)"))))
    (signals snowgrave:unclosed-class-operation
      (close-function-flow
       '(bad-function-update-flow)
       (append
        (replace-entry-body forms "FLOW-STORE-ENTRY"
                            (read-from-string "(progn (setf (flow-strict-store p) (make-instance 'flow-left :payload 1)) (incf (flow-strict-store p)))"))
        (read-from-string "((defun flow-strict-store (p) (declare (ignore p)) 3)
                            (defun (setf flow-strict-store) (value p) (declare (ignore p)) (slot-value value 'payload)))"))))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-flow.lisp" root))
           (metadata (merge-pathnames ".build/fresh-flow.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh helper domain flow executed."
                     (uiop:run-program (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                                             (namestring (merge-pathnames "scripts/fresh-flow.lisp" root))
                                             (namestring source) (namestring metadata)) :output :string))))))

(defun return-flow-forms ()
  (let ((*package* (find-package :snowgrave.fixture)))
    (append
     (function-flow-forms)
     (read-from-string
      "((defun return-id (p) p)
         (defun return-chain (p)
           (let* ((q (return-id p)) (r q)) (values r :secondary)))
         (defun return-choice (p q flag) (if flag p q))
         (defun return-recur (p n) (if (zerop n) p (return-recur p (1- n))))
         (defun return-escape (p flag) (when flag (return-from return-escape p)) p)
         (defun return-build (n) (make-instance 'flow-left :payload n))
         (defun return-forward (p) (return-id p))
         (defun return-tuple (p n) (flow-leaf p n))
         (defun return-never (p) (return-never p))
         (defun return-cycle-entry (p flag) (if flag p (return-never p)))
         (defun return-doc-only () \"ordinary text\")
         (defun return-doc-empty () \"documentation\" (declare (optimize speed)))
         (defun return-doc-entry () (values (return-doc-only) (return-doc-empty)))
         (defgeneric return-method (p flag))
         (defmethod return-method ((p flow-base) (flag t))
           (when flag (return-from return-method (values (slot-value p 'payload) :early)))
           (values (slot-value p 'payload) :normal))
         (defun return-method-entry (p flag) (return-method p flag))
         (defun return-store (p) (slot-value p 'payload))
         (defun (setf return-store) (n p)
           (when (zerop n) (return-from return-store (setf (slot-value p 'payload) n)))
           (setf (slot-value p 'payload) n))
         (defun return-write-entry (p n) (values (setf (return-store p) n) (return-store p)))
         (defun return-entry (p n)
           (let ((q (return-chain p)))
             (values (return-tuple (return-forward q) n)
                     (slot-value (return-recur p 2) 'payload)
                     (slot-value (return-build n) 'payload)
                     (slot-value (return-escape p t) 'payload))))
         (defun return-union-entry (p q flag)
           (slot-value (return-choice p q flag) 'payload))
         (defun return-indirect-entry (p)
           (values (slot-value (funcall #'return-forward p) 'payload)
                   (slot-value (apply #'return-forward (list p)) 'payload)))
         (defun return-values-entry (p) (return-chain p)))"))))

(defun close-return-flow (identity &optional (forms (return-flow-forms)))
  (let ((*package* (find-package :snowgrave.fixture)))
    (snowgrave:close-source-unit
     (list :forms forms) :unit-name identity
     :closed-classes (read-from-string "(flow-base flow-left flow-right)")
     :universe (read-from-string "(flow-base flow-left flow-right number)")
     :closed-generics (read-from-string "(flow-value return-method)")
     :entries (read-from-string "(flow-entry-left flow-entry-right flow-funcall-entry flow-apply-entry flow-optional-entry flow-store-entry flow-increment-entry flow-log-entry return-entry return-union-entry return-indirect-entry return-values-entry return-cycle-entry return-method-entry return-write-entry return-doc-entry)")
     :external-domains (read-from-string
                        "((flow-entry-left (flow-left number)) (flow-entry-right (flow-right number))
                          (flow-funcall-entry (flow-left number)) (flow-apply-entry (flow-left number))
                          (flow-optional-entry (flow-left number)) (flow-store-entry (flow-left number))
                          (flow-increment-entry (flow-left number)) (flow-log-entry ())
                          (return-entry (flow-left number)) (return-union-entry (flow-left flow-right t))
                          (return-indirect-entry (flow-left)) (return-values-entry (flow-left))
                          (return-cycle-entry (flow-left t)) (return-method-entry (flow-left t))
                          (return-write-entry (flow-left number)) (return-doc-entry ()))"))))

(defun return-flow-tests ()
  (let* ((*package* (find-package :snowgrave.fixture))
         (forms (return-flow-forms))
         (unit (close-return-flow '(return-flow :version 1) forms))
         (evidence (getf (snowgrave:unit-metadata unit) :ordinary-function-flow))
         (log (intern "*FLOW-LOG*" *package*))
         (payload (intern "PAYLOAD" *package*))
         (left (intern "FLOW-LEFT" *package*))
         (right (intern "FLOW-RIGHT" *package*))
         (proofs (getf evidence :functions)))
    (check (eq (getf evidence :primary-return-method) :monotone-normal-and-explicit-escape-union))
    (check (equal evidence (getf (snowgrave:unit-report unit) :ordinary-function-flow)))
    (check (eq (getf (find "RETURN-CHAIN" proofs :key #'proof-name :test #'equal)
                      :primary-return-domain) left))
    (check (equal (getf (find "RETURN-CHOICE" proofs :key #'proof-name :test #'equal)
                         :primary-return-domain) (list 'or left right)))
    (check (eq (getf (find "RETURN-RECUR" proofs :key #'proof-name :test #'equal)
                      :primary-return-domain) left))
    (check (eq (car (getf (find "RETURN-TUPLE" proofs :key #'proof-name :test #'equal)
                           :required-domains)) left))
    (check (eq (getf (find "RETURN-NEVER" proofs :key #'proof-name :test #'equal)
                      :primary-return-domain) :unknown))
    (check (equal (getf (find "RETURN-DOC-EMPTY" proofs :key #'proof-name :test #'equal)
                         :primary-return-domain) '(eql nil)))
    (dolist (form forms) (eval form))
    (check (equal (multiple-value-list (funcall (intern "RETURN-DOC-ENTRY" *package*)))
                  (multiple-value-list (funcall (test-unit-function unit 'return-doc-entry)))))
    (check (equal (multiple-value-list (funcall (test-unit-function unit 'return-doc-entry))) '("ordinary text" nil)))
    (let* ((native-left (make-instance left :payload 17))
           (native-right (make-instance right :payload 23))
           (records (loop for class in (list left right)
                          for value in '(17 23)
                          for description = (find class (getf (snowgrave:unit-metadata unit) :record-layouts)
                                                  :key (lambda (layout) (getf layout :class)))
                          for record = (snowgrave:sg-make-record
                                        (snowgrave:make-layout (getf description :identity) class
                                                              (getf description :ancestors) (getf description :slots)
                                                              :error-mapping (getf description :error-mapping)))
                          do (snowgrave:sg-record-write record payload value)
                          collect record)))
      (dolist (number '(0 3 -2 1/2))
        (let (native-values native-log)
          (progv (list log) (list nil)
            (setf native-values (multiple-value-list (funcall (intern "RETURN-ENTRY" *package*) native-left number))
                  native-log (reverse (symbol-value log))))
          (progv (list log) (list nil)
            (check (equal native-values (multiple-value-list (funcall (test-unit-function unit 'return-entry) (first records) number))))
            (check (equal native-log (reverse (symbol-value log)))))))
      (dolist (flag '(nil t))
        (check (= (funcall (intern "RETURN-UNION-ENTRY" *package*) native-left native-right flag)
                  (funcall (test-unit-function unit 'return-union-entry) (first records) (second records) flag)))
        (check (equal (multiple-value-list (funcall (intern "RETURN-METHOD-ENTRY" *package*) native-left flag))
                      (multiple-value-list (funcall (test-unit-function unit 'return-method-entry) (first records) flag)))))
      (check (equal (multiple-value-list (funcall (test-unit-function unit 'return-indirect-entry) (first records))) '(17 17)))
      (let ((values (multiple-value-list (funcall (test-unit-function unit 'return-values-entry) (first records)))))
        (check (eq (first values) (first records)))
        (check (eq (second values) :secondary)))
      (check (eq (funcall (test-unit-function unit 'return-cycle-entry) (first records) t) (first records)))
      (dolist (number '(0 7))
        (check (= (funcall (intern "RETURN-WRITE-ENTRY" *package*) native-left number)
                  (funcall (test-unit-function unit 'return-write-entry) (first records) number)))
        (check (= (slot-value native-left payload) (snowgrave:sg-record-read (first records) payload)))))
    ;; All these alternate return paths must broaden the primary proof. They
    ;; cannot silently disappear behind the known class at the end of the body.
    (dolist (body '("(when flag (return-from return-escape :foreign)) p"
                    "(block inner (when flag (return-from return-escape :foreign)) p)"
                    "(unwind-protect p (when flag (return-from return-escape :foreign)))"
                    "(let ((p :foreign)) (when flag (return-from return-escape p))) p"
                    "(flet ((escape (p) (return-from return-escape p))) (escape :foreign)) p"
                    "(handler-case p (error (p) (return-from return-escape p)))"
                    "(locally (declare (special p)) (when flag (return-from return-escape p))) p"
                    "(return-never p)"))
      (signals snowgrave:unclosed-class-operation
        (close-return-flow (list 'bad-return-flow body)
                           (replace-entry-body forms "RETURN-ESCAPE" (cons 'progn (read-from-string (concatenate 'string "(" body ")")))))))
    ;; Local functions cannot borrow the same-named global's narrower summary.
    (signals snowgrave:unclosed-class-operation
      (close-return-flow '(shadowed-return-helper)
                         (replace-entry-body forms "RETURN-INDIRECT-ENTRY"
                                             (read-from-string "(flet ((return-forward (p) (declare (ignore p)) :foreign)) (slot-value (return-forward p) 'payload))"))))
    (signals snowgrave:unclosed-class-operation
      (close-return-flow '(declared-special-return)
                         (replace-entry-body forms "RETURN-ESCAPE" (read-from-string "(locally (declare (special p)) p)"))))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-return-flow.lisp" root))
           (metadata (merge-pathnames ".build/fresh-return-flow.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh primary return flow executed."
                     (uiop:run-program (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                                             (namestring (merge-pathnames "scripts/fresh-return-flow.lisp" root))
                                             (namestring source) (namestring metadata)) :output :string))))))

(defun logical-function-type-tests ()
  (let* ((*package* (find-package :snowgrave.fixture))
         (forms (read-from-string
                 "((defgeneric logical-callable (x))
                    (defmethod logical-callable ((x t)) x)
                    (defgeneric callable-kind (x))
                    (defmethod callable-kind ((x t)) :other)
                    (defmethod callable-kind ((x function)) :function)
                    (defparameter *callable-count* 0)
                    (defun callable-result () #'logical-callable)
                    (defun callable-observation ()
                      (let ((f #'logical-callable))
                        (values (typep f 'function) (typep f 'compiled-function)
                                (callable-kind f) (callable-kind (callable-result))
                                (callable-kind #'identity))))
                    (defun callable-input (f) (values (typep f 'compiled-function) (callable-kind f)))
                    (defun callable-once ()
                      (let ((*callable-count* 0))
                        (values (typep (progn (incf *callable-count*) #'logical-callable) 'compiled-function)
                                *callable-count*))))"))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(logical-function-types)
                :universe '(function)
                :closed-generics (read-from-string "(logical-callable callable-kind)")
                :entries (read-from-string "(callable-result callable-observation callable-input callable-once)")
                :external-domains (read-from-string "((callable-result ()) (callable-observation ()) (callable-input (function)) (callable-once ()))"))))
    (dolist (form forms) (eval form))
    (check (equal (multiple-value-list (funcall (intern "CALLABLE-OBSERVATION" *package*)))
                  (multiple-value-list (funcall (test-unit-function unit 'callable-observation)))))
    (check (equal (multiple-value-list (funcall (test-unit-function unit 'callable-observation)))
                  '(t nil :function :function :function)))
    (check (equal (multiple-value-list (funcall (test-unit-function unit 'callable-input)
                                             (funcall (test-unit-function unit 'callable-result))))
                  '(nil :function)))
    (check (equal (multiple-value-list (funcall (test-unit-function unit 'callable-input) #'identity))
                  '(t :function)))
    (check (equal (multiple-value-list (funcall (test-unit-function unit 'callable-once))) '(nil 1)))
    (let ((generic (fdefinition (intern "LOGICAL-CALLABLE" *package*))))
      (check (equal (multiple-value-list (funcall (intern "CALLABLE-INPUT" *package*) generic))
                    (multiple-value-list (funcall (test-unit-function unit 'callable-input) generic)))))
    (signals snowgrave:incomplete-domain
      (snowgrave:close-source-unit
       (list :forms forms) :unit-name '(unsupported-native-function-class)
       :universe '(function standard-generic-function)
       :closed-generics (read-from-string "(logical-callable callable-kind)")
       :entries (read-from-string "(callable-result)") :external-domains (read-from-string "((callable-result ()))")))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-callable-types.lisp" root))
           (metadata (merge-pathnames ".build/fresh-callable-types.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh logical callable types executed."
                     (uiop:run-program (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                                             (namestring (merge-pathnames "scripts/fresh-callable-types.lisp" root))
                                             (namestring source) (namestring metadata)) :output :string))))))

(defun compiled-root-audit-tests ()
  (let* ((open (make-package "SNOWGRAVE.AUDIT.BUILDER" :use '(:cl)))
         (output (make-package "SNOWGRAVE.AUDIT.OUTPUT" :use '(:cl)))
         (class-name (intern "CAPTURED-CLASS" open))
         (generic-name (intern "CAPTURED-GENERIC" open))
         (build (snowgrave.sbcl::make-build :identity '(compiled-root-audit)
                                           :open-package open :output-package output))
         (capture-maker (compile nil '(lambda (value) (lambda () value)))))
    (unwind-protect
         (progn
           (eval `(cl:defclass ,class-name () ((payload))))
           (eval `(cl:defgeneric ,generic-name (x)))
           (eval `(cl:defmethod ,generic-name ((x ,class-name)) x))
           (let* ((class (find-class class-name))
                  (generic (fdefinition generic-name))
                  (method (first (sb-mop:generic-function-methods generic))))
             (sb-mop:finalize-inheritance class)
             (dolist (object (list class generic method
                                   (first (sb-mop:class-slots class))
                                   (sb-mop:generic-function-method-combination generic)
                                   (sb-kernel:find-layout class-name)
                                   class-name open))
               (signals snowgrave:residual-metaobject
                 (snowgrave.sbcl::compiled-root-audit
                  build (list (cons :capture (funcall capture-maker (vector (list object))))) nil)))
             ;; A displaced view hides a bad value outside its logical slice.
             ;; The backing vector is still a physical captured root.
             (let* ((backing (vector class :visible))
                    (view (make-array 1 :displaced-to backing :displaced-index-offset 1)))
               (signals snowgrave:residual-metaobject
                 (snowgrave.sbcl::compiled-root-audit build (list (cons :view (funcall capture-maker view))) nil)))
             (signals snowgrave:residual-metaobject
               (snowgrave.sbcl::compiled-root-audit build nil (list (list 'published t (list generic)))))
             (signals snowgrave:residual-metaobject
               (snowgrave.sbcl::compiled-root-audit build (list (cons :unknown (funcall capture-maker (make-hash-table)))) nil)))
           (signals snowgrave:residual-metaobject
             (snowgrave.sbcl::compiled-root-audit
              build (list (cons :undeclared-call (compile nil '(lambda () (snowgrave.tests::compiler-capture-operation 7))))) nil))
           (let ((missing (intern "MISSING-COMPILED-CALLEE" output)))
             (dolist (name (list missing (list 'setf missing)))
               (let* ((function (compile nil `(lambda () (declare (ftype (function () t) ,name)) (funcall #',name))))
                      (references (snowgrave.sbcl::compiled-code-linkage-references build (sb-kernel:fun-code-header function)))
                      (condition (handler-case
                                    (snowgrave.sbcl::compiled-root-audit build (list (cons :undefined-call function)) nil)
                                   (snowgrave:residual-metaobject (condition) condition))))
                 (check (some (lambda (reference)
                                (equal name (if (sb-kernel:fdefn-p reference) (sb-kernel:fdefn-name reference) reference))) references))
                 (check (typep condition 'snowgrave:residual-metaobject))
                 (check (eq (snowgrave:error-feature condition) :compiled-undefined-call))))
             (let* ((function (compile nil `(lambda () ',missing)))
                    (evidence (snowgrave.sbcl::compiled-root-audit build (list (cons :logical-name function)) nil)))
               (check (null (getf evidence :trust-boundaries)))
               (check (eq (funcall function) missing))))
           (let* ((function (compile nil '(lambda (form) (eval form))))
                  (code (sb-kernel:fun-code-header function)))
             (check (some (lambda (reference)
                            (eq 'eval (if (sb-kernel:fdefn-p reference)
                                          (sb-kernel:fdefn-name reference) reference)))
                          (snowgrave.sbcl::compiled-code-linkage-references build code)))
             (signals snowgrave:residual-metaobject
               (snowgrave.sbcl::compiled-root-audit build (list (cons :native-reflection function)) nil)))
           (let* ((graph (vector nil 17))
                  (closure (funcall capture-maker graph)))
             (setf (aref graph 0) graph)
             (let ((evidence (snowgrave.sbcl::compiled-root-audit build (list (cons :safe closure)) nil)))
               (check (plusp (getf evidence :closures)))
               (check (null (getf evidence :builder-objects)))
               (check (snowgrave.sbcl::serializable-tree-p evidence))
               (check (eq (funcall closure) graph)))))
      (snowgrave.sbcl::clean-package open)
      (snowgrave.sbcl::clean-package output)))
  ;; This compiler macro runs only during the closed compilation. It injects
  ;; a pass-one generic behind otherwise admitted external-call source. The
  ;; actual compiled-root gate must reject it before any publication.
  (let* ((*package* (find-package :snowgrave.fixture))
         (identity '(compiler-injected-builder-capture))
         (forms (remove-if (lambda (form)
                             (or (and (eq (car form) 'defun)
                                      (not (string= (symbol-name (cadr form)) "RUN")))
                                 (and (member (car form) '(defvar defparameter))
                                      (string= (symbol-name (cadr form)) "*CAPTURED*"))))
                           (replace-entry-body (fixture-forms) "RUN"
                                               (read-from-string "(snowgrave.tests::compiler-capture-operation n)"))))
         (original (compiler-macro-function 'compiler-capture-operation))
         (*injected-compiler-capture* nil))
    (unwind-protect
         (progn
           (setf (compiler-macro-function 'compiler-capture-operation)
                 (lambda (form environment)
                   (declare (ignore environment))
                   (let* ((package (find-package (format nil "SNOWGRAVE.BUILDER.~D" snowgrave.sbcl::*builder-counter*)))
                          (symbol (and package (snowgrave.sbcl::mapped-name (intern "ACCOUNT" :snowgrave.fixture) package))))
                     (if (and symbol (fboundp symbol))
                         (progn (setf *injected-compiler-capture* (fdefinition symbol))
                                '(load-time-value snowgrave.tests::*injected-compiler-capture* t))
                         form))))
           (let ((condition
                   (handler-case
                       (snowgrave:close-source-unit
                        (list :forms forms) :unit-name identity
                        :closed-classes (read-from-string "(policy fast)") :universe (read-from-string "(policy fast number)")
                        :closed-generics (read-from-string "(account value (setf value))")
                        :entries (read-from-string "(run)") :external-domains (read-from-string "((run (policy number)))")
                        :external-operations '(snowgrave.tests::compiler-capture-operation)
                        :external-return-domains '((snowgrave.tests::compiler-capture-operation (number))))
                     (snowgrave:residual-metaobject (condition) condition))))
             (check (typep condition 'snowgrave:residual-metaobject))
             (check (eq (snowgrave:error-phase condition) :compiled-residual-audit)))
           (check (not (find-package (format nil "SNOWGRAVE.UNIT.~A" (with-standard-io-syntax (write-to-string identity))))))
           (check (not (gethash (with-standard-io-syntax (write-to-string identity)) snowgrave.sbcl::*published-identities*))))
      (setf (compiler-macro-function 'compiler-capture-operation) original)))
  ;; An actual constant function-cell load has no named linkage fixup when
  ;; its symbol/SETF cell is currently unbound. It must not become an ignored
  ;; logical atom and permit a later arbitrary generic binding after closure.
  (let* ((identity '(compiler-injected-undefined-call))
         (missing (gentemp "MISSING-COMPILED-TARGET-" *package*))
         (original (compiler-macro-function 'compiler-capture-operation)))
    (unwind-protect
         (progn
           (setf (compiler-macro-function 'compiler-capture-operation)
                 (lambda (form environment)
                   (declare (ignore environment))
                   `(locally (declare (ftype (function (t) t) ,missing)) (,missing ,(second form)))))
           (let ((condition (handler-case
                              (snowgrave:close-source-unit
                               (list :forms '((defun unbound-compiled-entry (x) (compiler-capture-operation x))))
                               :unit-name identity :universe '(number) :entries '(unbound-compiled-entry)
                               :external-domains '((unbound-compiled-entry (number)))
                               :external-operations '(compiler-capture-operation))
                             (snowgrave:residual-metaobject (condition) condition))))
             (check (typep condition 'snowgrave:residual-metaobject))
             (check (eq (snowgrave:error-feature condition) :compiled-undefined-call))
             (check (eq (snowgrave:error-phase condition) :compiled-residual-audit)))
           (check (not (find-package (format nil "SNOWGRAVE.UNIT.~A" (with-standard-io-syntax (write-to-string identity))))))
           (check (not (gethash (with-standard-io-syntax (write-to-string identity)) snowgrave.sbcl::*published-identities*))))
      (setf (compiler-macro-function 'compiler-capture-operation) original)
      (unintern missing)))
  (let* ((unit (close-fixture '(compiled-audit-positive)))
         (evidence (getf (snowgrave:unit-report unit) :compiled-root-evidence)))
    (check (plusp (getf evidence :constant-edges)))
    (check (equal (getf (snowgrave:unit-metadata unit) :compiler-dependencies) (getf evidence :trust-boundaries)))))

(defpackage #:snowgrave.namespace.a
  (:use #:cl) (:shadow #:identity)
  (:shadowing-import-from #:snowgrave #:defclass #:defgeneric #:defmethod))
(defpackage #:snowgrave.namespace.b
  (:use #:cl)
  (:shadowing-import-from #:snowgrave #:defclass #:defgeneric #:defmethod))

(defpackage #:snowgrave.mutable.fixture
  (:use #:cl)
  (:shadowing-import-from #:snowgrave #:defgeneric #:defmethod))

(defvar *mutable-foreign-invoked* nil)
(defvar *mutable-effect-count* 0)
(cl:defgeneric mutable-foreign-function (x))
(cl:defmethod mutable-foreign-function ((x t))
  (setf *mutable-foreign-invoked* t) (list :foreign x))
(defun mutate-callable-binding ()
  (incf *mutable-effect-count*)
  (setf (symbol-value (intern "*CALLABLE*" :snowgrave.mutable.fixture)) #'mutable-foreign-function))
(defun mutate-declared-binding ()
  (incf *mutable-effect-count*)
  (setf (symbol-value (intern "CALLBACK" :snowgrave.mutable.fixture)) #'mutable-foreign-function))
(defun mutate-ambient-binding ()
  (incf *mutable-effect-count*)
  (setf (symbol-value (intern "AMBIENT" :snowgrave.mutable.fixture)) #'mutable-foreign-function))

(defun mutable-special-tests ()
  (let* ((*package* (find-package :snowgrave.mutable.fixture))
         (generic (intern "LOCAL-FUNCTION" *package*))
         (entry (intern "MUTABLE-ENTRY" *package*))
         (callable (intern "*CALLABLE*" *package*))
         (callback (intern "CALLBACK" *package*))
         (ambient (intern "AMBIENT" *package*))
         (prefix (read-from-string
                  "((defgeneric local-function (x))
                     (defmethod local-function ((x t)) (list :local x)))")))
    (labels ((forms (body &optional source-special)
               (append prefix
                       (when source-special (read-from-string "((defparameter *callable* (load-time-value #'local-function)))"))
                       (list `(defun ,entry (,(intern "X" *package*)) ,(read-from-string body)))))
             (close-it (name forms)
               (snowgrave:close-source-unit
                (list :forms forms) :unit-name name :closed-generics (list generic)
                :universe '(t) :entries (list entry) :external-domains (list (list entry '(t)))
                :external-operations '(mutate-callable-binding mutate-declared-binding mutate-ambient-binding))))
      ;; Execute the actual native counterexample, including the external's
      ;; mutation/effect, before asserting that closure rejects the program.
      (let ((forms (forms "(let ((*callable* #'local-function)) (snowgrave.tests::mutate-callable-binding) (funcall *callable* x))" t)))
        (dolist (form forms) (eval form))
        (let ((*mutable-foreign-invoked* nil) (*mutable-effect-count* 0))
          (check (equal (funcall entry 7) '(:foreign 7)))
          (check *mutable-foreign-invoked*)
          (check (= *mutable-effect-count* 1)))
        (signals snowgrave:unclosed-call (close-it '(mutable-special-native-counterexample) forms)))
      (dolist (body '("(let ((*callable* #'local-function)) (snowgrave.tests::mutate-callable-binding) (apply *callable* (list x)))"
                      "(let ((*callable* #'local-function)) (snowgrave.tests::mutate-callable-binding) (mapcar *callable* (list x)))"
                      "(let ((*callable* #'local-function)) (snowgrave.tests::mutate-callable-binding) (find x (list x) :key *callable*))"
                      "(let* ((*callable* #'local-function)) (snowgrave.tests::mutate-callable-binding) (funcall *callable* x))"))
        (signals snowgrave:unclosed-call (close-it (list 'mutable-special body) (forms body t))))
      (dolist (body '("(let ((callback #'local-function)) (declare (special callback)) (snowgrave.tests::mutate-declared-binding) (funcall callback x))"
                      "(let ((callback #'local-function)) (locally (declare (special callback)) (snowgrave.tests::mutate-declared-binding) (funcall callback x)))"
                      "(let ((callback #'local-function)) (declare (special callback)) (mapcar callback (list x)))"))
        (signals snowgrave:unclosed-call (close-it (list 'declared-special body) (forms body))))
      (proclaim `(special ,ambient))
      (signals snowgrave:unclosed-call
        (close-it '(ambient-proclaimed-special)
                  (forms "(let ((ambient #'local-function)) (snowgrave.tests::mutate-ambient-binding) (funcall ambient x))")))
      ;; A true lexical capture remains callable even though that same external
      ;; changes a distinct special cell. Its effect must still run once.
      (let* ((unit (close-it '(lexical-capture-external-effects)
                            (forms "(let ((callback #'local-function)) (snowgrave.tests::mutate-declared-binding) (funcall callback x))")))
             (*mutable-foreign-invoked* nil) (*mutable-effect-count* 0))
        (check (equal (funcall (snowgrave:unit-function unit entry) 7) '(:local 7)))
        (check (not *mutable-foreign-invoked*))
        (check (= *mutable-effect-count* 1))
        (check (eq (symbol-value callback) #'mutable-foreign-function)))
      ;; Closing rejection leaves all existing source and external cells alone.
      (check (eq (symbol-value callback) #'mutable-foreign-function))
      (check (fboundp generic))
      (check (boundp callable)))))

(defun source-owner-tests ()
  (let* ((name (intern "SAME" :snowgrave.namespace.a))
         (other (intern "SAME" :snowgrave.namespace.b))
         (forms `((snowgrave:defclass ,name () ())
                  (defun ,name (x) x)
                  (defvar ,name 0)
                  (snowgrave:defgeneric ,other (x))
                  (snowgrave:defmethod ,other ((x t)) 1)
                  (snowgrave:defmethod ,other ((x t)) 2)
                  (defun (setf ,name) (new x) (declare (ignore x)) new)))
         (source (snowgrave:make-authored-source forms :identity '(portable-source :version 1)))
         (definitions (snowgrave:authored-source-definitions source)))
    (check (equal (mapcar #'snowgrave:authored-definition-position definitions) '(1 2 3 4 5 6 7)))
    (check (equal (snowgrave:authored-source-forms source) forms))
    (check (not (eq (snowgrave:authored-source-forms source) forms)))
    (setf (caddr (third forms)) :caller-mutation)
    (check (eql (caddr (snowgrave:authored-definition-form
                        (snowgrave:find-authored-definition source :global name))) 0))
    (check (eq (snowgrave:authored-definition-kind (snowgrave:find-authored-definition source :class name)) :class))
    (check (eq (snowgrave:authored-definition-kind (snowgrave:find-authored-definition source :function name)) :function))
    (check (not (snowgrave:find-authored-definition source :function other)))
    (check (= (snowgrave:authored-definition-position (snowgrave:find-authored-definition source :method other)) 6))
    (check (equal (mapcar #'snowgrave:authored-definition-position (snowgrave:authored-source-definitions source :method)) '(6 5)))
    (check (= (snowgrave:authored-form-position source (seventh (snowgrave:authored-source-forms source))) 7))
    (check (equal (snowgrave:authored-source-specials source) (list name)))
    (check (snowgrave:find-authored-definition source :function (list 'setf name)))
    (let* ((plain `((cl:defclass ,name () ()) (cl:defgeneric ,other (x))
                    (cl:defmethod ,other ((x t)) x)))
           (owner (snowgrave:make-authored-source plain)))
      (check (equal (mapcar #'snowgrave:authored-definition-kind (snowgrave:authored-source-definitions owner))
                    '(:class :generic :method)))
      (check (equal (snowgrave:authored-source-forms owner) plain))
      (check (not (snowgrave:source-defining-kind `(,(make-symbol "DEFCLASS") ,name () ()))))
      (signals snowgrave:nonreproducible-source
        (snowgrave:make-authored-source `((snowgrave:defclass ,name () ()) (cl:defclass ,name () ())))))
    (let* ((repeat `(cl:defmethod ,other ((x t)) x))
           (owner (snowgrave:make-authored-source (list repeat (copy-tree repeat)))))
      (check (= 1 (snowgrave:authored-form-position owner (first (snowgrave:authored-source-forms owner)))))
      (check (= 2 (snowgrave:authored-form-position owner (second (snowgrave:authored-source-forms owner))))))
    (let ((condition (handler-case
                         (snowgrave:make-authored-source `((defun ,name () 1) (defun ,name () 2)) :identity '(duplicate-source))
                       (snowgrave:nonreproducible-source (condition) condition))))
      (check (typep condition 'snowgrave:nonreproducible-source))
      (check (equal (snowgrave:error-source-key condition) '((duplicate-source) 2))))
    (let ((cycle (list '(defun placeholder () 1))))
      (setf (cdr cycle) cycle)
      (signals snowgrave:nonreproducible-source (snowgrave:make-authored-source cycle)))
    (signals snowgrave:unsupported-definition (snowgrave:make-authored-source '(42)))
    (let* ((contract (snowgrave:source-lambda-contract '(x &optional (o 3 op) &rest r &key ((:named k) 5 kp) &allow-other-keys &aux (a 7))))
           (body '((declare (special callback)) "documentation" (funcall callback x))))
      (check (equal (getf contract :variables) '(x o op r k kp a)))
      (check (equal (getf contract :required) '(x)))
      (check (equal (getf contract :keys) '(((:named k) 5 kp))))
      (check (equal (snowgrave:source-body-special-domains body) '((callback . :unknown))))
      (multiple-value-bind (prefix executable) (snowgrave:source-body-parts body)
        (check (equal prefix '((declare (special callback)) "documentation")))
        (check (equal executable '((funcall callback x)))))
      (check (equal (snowgrave:source-block-body (list 'setf name) '((values 1 :tag)))
                    `((block ,name (values 1 :tag))))))
    (dolist (case '((((:primary)) nil (:provided :unknown :unknown))
                    (nil nil (:unknown :unknown :unknown))
                    (nil t (:missing :missing :missing))))
      (destructuring-bind (facts completep kinds) case
        (multiple-value-bind (scope processed)
            (snowgrave::analyze-source-multiple-value-bindings
             '(a b c) :producer nil
             (lambda (producer scope) (declare (ignore scope)) (values facts producer completep))
             (lambda (name kind fact scope) (acons name (list kind fact) scope)))
          (check (eq processed :producer))
          (check (equal (mapcar (lambda (name) (car (cdr (assoc name scope)))) '(a b c)) kinds)))))
    (let* ((root (asdf:system-source-directory "snowgrave")))
      (check (search "Portable source owner executed."
                     (uiop:run-program (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                                             (namestring (merge-pathnames "scripts/fresh-source-owner.lisp" root))) :output :string))))))

(defpackage #:snowgrave.retention.fixture
  (:use #:cl)
  (:shadowing-import-from #:snowgrave #:defgeneric #:defmethod))

(defun flow-retention-tests ()
  (let ((package (find-package :snowgrave.retention.fixture)) results)
    (dolist (count '(3 25))
      (let* ((*package* package)
             (generic (intern "VALUE" package))
             (entry (intern "ENTRY" package))
             (x (intern "X" package))
             (helpers (loop for index below count collect (intern (format nil "HELPER-~D" index) package)))
             (forms (append (list `(snowgrave:defgeneric ,generic (,x))
                                  `(snowgrave:defmethod ,generic ((,x t)) ,x))
                            (loop for helper in helpers for tail on helpers
                                  collect `(defun ,helper (,x) ,(if (cdr tail) `(,(second tail) ,x) x)))
                            (list `(defun ,entry (,x) (,generic (,(first helpers) ,x))))))
             (unit (snowgrave:close-source-unit
                    (list :forms forms) :unit-name (list 'flow-retention :length count)
                    :universe '(t) :closed-generics (list generic) :entries (list entry)
                    :external-domains (list (list entry '(t)))))
             (metadata (snowgrave:unit-metadata unit))
             (output (find-package (first (getf (first (getf metadata :entries)) :code-key))))
             (owned-symbols (loop for symbol being the present-symbols of output count t))
             (iterations (getf (getf metadata :ordinary-function-flow) :iterations)))
        (check (= (funcall (snowgrave:unit-function unit entry) 17) 17))
        (check (eq (funcall (snowgrave:unit-function unit entry) :arbitrary) :arbitrary))
        (check (>= iterations count))
        (push (list iterations (- owned-symbols (1+ count))) results)))
    (check (> (first (first results)) (first (second results))))
    ;; Extra fixed-point iterations cannot permanently intern another whole
    ;; generation of private method/cell names in the installed code package.
    (check (= (second (first results)) (second (second results))))))

(defun binding-owner-tests ()
  (let ((bindings '((x 1) (y x) (z y))) (outer '((x . 10) (y . 20) (z . 30))))
    (dolist (sequential '(nil t))
      (let (visited)
        (multiple-value-bind (scope processed)
            (snowgrave:analyze-source-bindings
             bindings sequential outer
             (lambda (name initializer scope)
               (push name visited)
               (values (if (symbolp initializer) (cdr (assoc initializer scope)) initializer) initializer))
             (lambda (name value scope) (acons name value scope)))
          (let ((native (eval `(let ((x 10) (y 20) (z 30))
                                (,(if sequential 'let* 'let) ,bindings (list x y z))))))
            (check (equal (mapcar (lambda (name) (cdr (assoc name scope))) '(x y z)) native))
            (check (equal (eval `(let ((x 10) (y 20) (z 30))
                                  (,(if sequential 'let* 'let) ,processed (list x y z)))) native)))
          (check (equal (nreverse visited) '(x y z)))
          (check (equal outer '((x . 10) (y . 20) (z . 30)))))))
    (let ((visits 0))
      (dolist (invalid (list '((x 1 2)) '((:constant 3)) '(nil)
                            (let ((cycle (list '(x 1)))) (setf (cdr cycle) cycle) cycle)))
        (let ((condition (handler-case
                             (snowgrave:analyze-source-bindings
                              invalid nil outer (lambda (&rest args) (declare (ignore args)) (incf visits))
                              (lambda (&rest args) (declare (ignore args))) :source-key '(binding-owner 1))
                           (snowgrave:unsupported-definition (condition) condition))))
          (check (typep condition 'snowgrave:unsupported-definition))
          (check (equal (snowgrave:error-source-key condition) '(binding-owner 1)))))
      (check (zerop visits)))))

(defpackage #:snowgrave.destructuring.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defgeneric #:defmethod))
(defun provide-foreign-callable () #'mutable-foreign-function)

(defpackage #:snowgrave.lambda-scope.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defgeneric #:defmethod))

(defun lambda-scope-tests ()
  (let* ((*package* (find-package :snowgrave.lambda-scope.fixture))
         (generic (intern "ONLY-LIST" *package*)) (entry (intern "ENTRY" *package*))
         (forms (read-from-string
                 "((defgeneric only-list (x))
                    (defmethod only-list ((x list)) :list)
                    (defun entry (r)
                      (funcall (lambda (&optional (x (only-list r)) &rest r)
                                 (declare (ignore r)) x))))")))
    (dolist (form forms) (eval form))
    (signals sb-pcl::no-applicable-method-error (funcall entry 7))
    (labels ((close-it (identity forms domain)
               (snowgrave:close-source-unit
                (list :forms forms) :unit-name identity :universe '(list)
                :closed-generics (list generic) :entries (list entry) :external-domains (list (list entry (list domain))))))
      (dolist (body '("(funcall (lambda (&optional (x (only-list r)) &rest r) (declare (ignore r)) x))"
                      "(flet ((use (&optional (x (only-list r)) &rest r) (declare (ignore r)) x)) (use))"
                      "(labels ((use (&optional (x (only-list r)) &rest r) (declare (ignore r)) x)) (use))"))
        (let ((condition (handler-case (close-it (list 'future-rest body) (replace-entry-body forms "ENTRY" (read-from-string body)) t)
                           (snowgrave:incomplete-domain (condition) condition))))
          (check (typep condition 'snowgrave:incomplete-domain))
          (check (eq (snowgrave:error-feature condition) :internal-call-domain))))
      (let ((unit (close-it '(future-rest-valid-outer-list) forms 'list)))
        (check (eq (funcall (snowgrave:unit-function unit entry) '(1 2)) :list)))))
  (let* ((*package* (find-package :snowgrave.lambda-scope.fixture))
         (forms (read-from-string
                 "((defgeneric local-call (x))
                    (defmethod local-call ((x t)) (list :closed x))
                    (defun lambda-entry (x)
                      (let ((f #'local-call)) (funcall (lambda (&optional (a (funcall f x)) f) (declare (ignore f)) a))))
                    (defun key-entry (x)
                      (let ((f #'local-call)) (funcall (lambda (&key (a (funcall f x)) f) (declare (ignore f)) a))))
                    (defun local-entry (x)
                      (let ((f #'local-call)) (flet ((use (&optional (a (funcall f x)) f) (declare (ignore f)) a)) (use))))
                    (defun labels-entry (x)
                      (let ((f #'local-call)) (labels ((use (&optional (a (funcall f x)) f) (declare (ignore f)) a)) (use))))
                    (defun aux-entry (x &aux (f #'local-call)) (funcall f x))
                    (defun ordered-entry (x &aux (a (+ x 1)) (b (+ a 1))) b))"))
         (entries (mapcar (lambda (name) (intern name *package*))
                          '("LAMBDA-ENTRY" "KEY-ENTRY" "LOCAL-ENTRY" "LABELS-ENTRY" "AUX-ENTRY" "ORDERED-ENTRY")))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(lambda-initializer-captures)
                :universe '(t) :closed-generics (list (intern "LOCAL-CALL" *package*)) :entries entries
                :external-domains (mapcar (lambda (name) (list name '(t))) entries))))
    (dolist (form forms) (eval form))
    (dolist (entry entries)
      (check (equal (funcall (snowgrave:unit-function unit entry) 7) (funcall entry 7))))
    (let ((source (merge-pathnames ".build/fresh-lambda-scopes.lisp" (asdf:system-source-directory "snowgrave")))
          (data (merge-pathnames ".build/fresh-lambda-scopes.metadata" (asdf:system-source-directory "snowgrave"))))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream data :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh lambda initializer scopes executed."
              (uiop:run-program
              (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                    (namestring (merge-pathnames "scripts/fresh-lambda-scopes.lisp" (asdf:system-source-directory "snowgrave")))
                    (namestring source) (namestring data)) :output :string))))
    (signals snowgrave:unclosed-call
      (snowgrave:close-source-unit
       (list :forms (replace-entry-body forms "AUX-ENTRY" (read-from-string "(locally (declare (special f)) (funcall f x))")))
       :unit-name '(lambda-local-special-aux) :universe '(t)
       :closed-generics (list (intern "LOCAL-CALL" *package*)) :entries (list (intern "AUX-ENTRY" *package*))
       :external-domains (list (list (intern "AUX-ENTRY" *package*) '(t))))))
  (let ((outer '((r . :outer-rest) (f . :outer-function))) (visited nil))
    (multiple-value-bind (scope ordinary initializers)
        (snowgrave:analyze-source-lambda-bindings
         '(x &optional (a r ap) (b a) &rest r &key ((:named k) r kp) &aux (z k)) outer
         (lambda (name initializer scope)
           (push (list name (cdr (assoc initializer scope))) visited)
           (values initializer initializer))
         (lambda (name kind fact scope) (acons name (if (eq kind :aux) fact kind) scope)))
      (check (equal (nreverse visited) '((a :outer-rest) (b :optional) (k :rest) (z :key))))
      (check (equal initializers '(r a r k)))
      (check (equal ordinary '(x &optional (a r ap) (b a) &rest r &key ((:named k) r kp) &aux (z k))))
      (check (eq (cdr (assoc 'ap scope)) :supplied-p))
      (check (eq (cdr (assoc 'z scope)) 'k))
      (check (equal outer '((r . :outer-rest) (f . :outer-function))))))
  (signals snowgrave:unsupported-definition (snowgrave:source-lambda-contract '(x &optional (y nil x))))
  (signals snowgrave:unsupported-definition (snowgrave:source-lambda-contract '(x &aux (nil 1))))
  (signals snowgrave:unsupported-definition (snowgrave:source-lambda-contract '(x &optional (y nil :constant))))
  (let ((cycle (list 'x)))
    (setf (cdr cycle) cycle)
    (signals snowgrave:unsupported-definition (snowgrave:source-lambda-contract cycle))))

(defun lambda-grammar-tests ()
  ;; Required specialization is DEFMETHOD syntax, never an ordinary binding.
  (dolist (arguments '(((x number)) ((x)) ((x number extra))
                       (x &rest (r nil)) (x &rest) (x &rest r extra)
                       (x &optional (y nil nil)) (x &key (y nil nil))
                       (x &optional &optional y) (x &key y &rest r)
                       (x &allow-other-keys) (x &key &allow-other-keys y)
                       (x &aux y &key z)))
    (signals snowgrave:unsupported-definition (snowgrave:source-lambda-contract arguments)))
  (let ((contract (snowgrave:source-lambda-contract
                   '((x number) (y (eql 7)) &optional (z y zp)) :specialized-required-p t)))
    (check (equal (getf contract :required) '(x y)))
    (check (equal (getf contract :ordinary) '(x y &optional (z y zp)))))
  (dolist (arguments '(((x)) ((x number extra)) ((x (eql))) ((x (eql 1 2)))))
    (signals snowgrave:unsupported-definition
      (snowgrave:source-lambda-contract arguments :specialized-required-p t)))
  (check (search "Fresh ordinary and method lambda grammars executed."
                 (uiop:run-program
                  (list "sbcl" "--dynamic-space-size" "2048" "--no-sysinit" "--no-userinit" "--script"
                        (namestring (merge-pathnames "scripts/fresh-lambda-grammar.lisp"
                                                     (asdf:system-source-directory "snowgrave"))))
                  :output :string))))

(defpackage #:snowgrave.callable-shadow.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defgeneric #:defmethod))

(defun callable-shadow-tests ()
  (let* ((*package* (find-package :snowgrave.callable-shadow.fixture))
         (generic (intern "ONLY-LIST" *package*)) (entry (intern "ENTRY" *package*))
         (base (read-from-string
                "((defgeneric only-list (x))
                   (defmethod only-list ((x list)) (list :list x))
                   (defun list-return () (list 1))
                   (defun number-return () 17))")))
    (labels ((close-it (forms identity entries)
               (snowgrave:close-source-unit
                (list :forms forms) :unit-name identity :universe '(list)
                :closed-generics (list generic) :entries entries
                :external-domains (mapcar (lambda (name) (list name nil)) entries))))
      (dolist (tail '("((defun entry () (let ((f #'list-return)) (only-list (let ((f #'number-return)) (funcall f))))))"
                      "((defun entry () (let ((f #'list-return)) (let* ((f #'number-return) (result (funcall f))) (only-list result)))))"
                      "((defun helper () (let ((f #'list-return)) (let ((f #'number-return)) (funcall f)))) (defun entry () (only-list (helper))))"
                      "((defun helper () (let ((f #'list-return)) (let ((f #'number-return)) (return-from helper (funcall f))))) (defun entry () (only-list (helper))))"))
        (let ((forms (append base (read-from-string tail))))
          (dolist (form forms) (eval form))
          (signals sb-pcl::no-applicable-method-error (funcall entry))
          (let ((condition (handler-case (close-it forms (list 'invalid-callable-shadow tail) (list entry))
                             (snowgrave:incomplete-domain (condition) condition))))
            (check (typep condition 'snowgrave:incomplete-domain))
            (check (eq (snowgrave:error-feature condition) :internal-call-domain)))))
      (let* ((forms
               (append base
                 (read-from-string
                  "((defun direct () (let ((f #'number-return)) (only-list (let ((f #'list-return)) (funcall f)))))
                     (defun sequential () (let ((f #'number-return)) (let* ((f #'list-return) (result (funcall f))) (only-list result))))
                     (defun parallel () (let ((f #'list-return)) (only-list (let ((f #'number-return) (result (funcall f))) (declare (ignore f)) result))))
                     (defun helper () (let ((f #'number-return)) (let ((f #'list-return)) (return-from helper (funcall f)))))
                     (defun returned () (only-list (helper))))")))
             (entries (mapcar (lambda (name) (intern name *package*)) '("DIRECT" "SEQUENTIAL" "PARALLEL" "RETURNED")))
             (unit (close-it forms '(valid-callable-shadow) entries))
             (root (asdf:system-source-directory "snowgrave"))
             (source (merge-pathnames ".build/fresh-callable-shadow.lisp" root))
             (metadata (merge-pathnames ".build/fresh-callable-shadow.metadata" root)))
        (dolist (form forms) (eval form))
        (dolist (entry entries)
          (check (equal (funcall (snowgrave:unit-function unit entry)) (funcall entry)))
          (check (equal (funcall entry) '(:list (1)))))
        (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
        (with-open-file (stream metadata :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
        (check (search "Fresh callable shadow scopes executed."
                       (uiop:run-program
                        (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                              (namestring (merge-pathnames "scripts/fresh-callable-shadow.lisp" root))
                              (namestring source) (namestring metadata)) :output :string)))))))

(defpackage #:snowgrave.callable-flow.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defgeneric #:defmethod))

(defun observe-unproved-callback (callback) (funcall callback :outside))

(defpackage #:snowgrave.callable-escape.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defgeneric #:defmethod))

(defun callable-reference-escape-tests ()
  (let* ((*package* (find-package :snowgrave.callable-escape.fixture))
         (generic (intern "VALUE" *package*)) (entry (intern "ENTRY" *package*))
         (base (read-from-string
                "((defgeneric value (x)) (defmethod value ((x number)) :numeric)
                   (defun helper (x) (value x)))")))
    (dolist (body '("(funcall (progn (snowgrave.tests::observe-unproved-callback #'helper) #'helper) x)"
                    "(funcall (let ((effect (snowgrave.tests::observe-unproved-callback #'helper)))
                                (declare (ignore effect)) #'helper) x)"
                    "(funcall (if x (progn (snowgrave.tests::observe-unproved-callback #'helper) #'helper) #'helper) x)"))
      (let* ((forms (append base (list `(defun ,entry (,(intern "X" *package*)) ,(read-from-string body)))))
             (condition nil))
        (dolist (form forms) (eval form))
        (signals sb-pcl::no-applicable-method-error (funcall entry 17))
        (setf condition
              (handler-case
                  (snowgrave:close-source-unit
                   (list :forms forms) :unit-name (list 'callback-expression-escape body)
                   :closed-generics (list generic) :universe '(number) :entries (list entry)
                   :external-domains (list (list entry '(number)))
                   :external-operations '(observe-unproved-callback))
                (snowgrave:incomplete-domain (condition) condition)))
        (check (typep condition 'snowgrave:incomplete-domain))
        (check (eq (snowgrave:error-feature condition) :internal-call-domain))))
    (let* ((entries (mapcar (lambda (name) (intern name *package*)) '("LITERAL-ENTRY" "LOAD-ENTRY")))
           (forms (append base (read-from-string
                                "((defun literal-entry (x) (funcall #'helper x))
                                   (defun load-entry (x) (funcall (load-time-value #'helper) x)))")))
           (unit (snowgrave:close-source-unit
                  (list :forms forms) :unit-name '(immediate-callable-reference) :closed-generics (list generic)
                  :universe '(number) :entries entries
                  :external-domains (mapcar (lambda (name) (list name '(number))) entries))))
      (dolist (form forms) (eval form))
      (dolist (name entries)
        (check (equal (multiple-value-list (funcall name 17))
                      (multiple-value-list (funcall (snowgrave:unit-function unit name) 17))))))))

(defun callable-flow-tests ()
  (let* ((*package* (find-package :snowgrave.callable-flow.fixture))
         (forms (read-from-string
                 "((defgeneric value (x))
                    (defmethod value ((x number)) (values (+ x 1) :generic-value))
                    (defun invoke (f x) (funcall f x))
                    (defun passthrough (f) f)
                    (defun callback () (load-time-value #'value))
                    (defun entry (x)
                      (values (list (invoke #'value x) (funcall (callback) x)
                                    (let* ((a #'value) (b a)) (invoke b x))
                                    (invoke (passthrough #'value) x)
                                    (multiple-value-bind (a b) (invoke #'value x) (list a b))) :entry-value)))"))
         (entry (intern "ENTRY" *package*)) (generic (intern "VALUE" *package*))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(named-callable-flow) :closed-generics (list generic)
                :universe '(number) :entries (list entry) :external-domains (list (list entry '(number)))))
         (flow (getf (snowgrave:unit-report unit) :ordinary-function-flow)))
    (dolist (form forms) (eval form))
    (dolist (argument '(17 1/2 #c(2 3)))
      (check (equal (multiple-value-list (funcall (snowgrave:unit-function unit entry) argument))
                    (multiple-value-list (funcall entry argument)))))
    (let* ((invoke (find "INVOKE" (getf flow :functions) :test #'string= :key #'proof-name))
           (pass (find "PASSTHROUGH" (getf flow :functions) :test #'string= :key #'proof-name)))
      (check (equal (first (getf invoke :required-domains)) (list :function-target generic)))
      (check (equal (getf pass :primary-return-domain) (list :function-target generic)))
      (check (equal flow (getf (snowgrave:unit-metadata unit) :ordinary-function-flow))))
    ;; This complete finite target set needs no arbitrary callable helper.
    ;; Exercise both branches; an uncalled INVOKE must not cause rejection.
    (let* ((mixed-forms (replace-entry-body forms "ENTRY"
                         (read-from-string "(funcall (if (eql x 0) #'value #'identity) x)")))
           (mixed (snowgrave:close-source-unit
                   (list :forms mixed-forms) :unit-name '(known-generic-and-ordinary-targets)
                   :closed-generics (list generic) :universe '(number)
                   :entries (list entry) :external-domains (list (list entry '(number))))))
      (dolist (form mixed-forms) (eval form))
      (dolist (argument '(0 17 #c(2 3)))
        (check (equal (multiple-value-list (funcall entry argument))
                      (multiple-value-list (funcall (snowgrave:unit-function mixed entry) argument))))))
    (dolist (body '("(invoke (if x #'value 17) x)"
                    "(let ((f #'value)) (locally (declare (special f)) (invoke f x)))"))
      (signals snowgrave:unclosed-call
        (snowgrave:close-source-unit
         (list :forms (replace-entry-body forms "ENTRY" (read-from-string body)))
         :unit-name (list 'unknown-callable-flow body) :closed-generics (list generic)
         :universe '(number) :entries (list entry) :external-domains (list (list entry '(number))))))
    (signals snowgrave:unclosed-call
      (snowgrave:close-source-unit
       (list :forms (append (butlast forms)
                           (list (read-from-string "(defun entry (f x) (invoke f x))"))))
       :unit-name '(unknown-external-callable-flow) :closed-generics (list generic)
       :universe '(number function) :entries (list entry) :external-domains (list (list entry '(function number)))))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-callable-flow.lisp" root))
           (metadata (merge-pathnames ".build/fresh-callable-flow.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh named callable flow executed."
                     (uiop:run-program
                      (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                            (namestring (merge-pathnames "scripts/fresh-callable-flow.lisp" root))
                            (namestring source) (namestring metadata)) :output :string))))))

(defpackage #:snowgrave.callable-union.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defgeneric #:defmethod))

(defun callable-union-tests ()
  (let* ((*package* (find-package :snowgrave.callable-union.fixture))
         (forms (read-from-string
                 "((defparameter *selections* 0)
                    (defgeneric left (x))
                    (defmethod left ((x number)) (values (+ x 1) :left))
                    (defgeneric right (x))
                    (defmethod right ((x number)) (values (- x 1) :right))
                    (defgeneric pair (x y))
                    (defmethod pair ((x number) (y number)) (+ x y))
                    (defun invoke (f x) (funcall f x))
                    (defun invoke-apply (f x) (apply f (list x)))
                    (defun invoke-values (f x) (multiple-value-call f (values x)))
                    (defun select-function (flag) (incf *selections*) (if flag #'left #'right))
                    (defun entry (flag x)
                      (values
                       (list (multiple-value-bind (a b) (funcall (select-function flag) x) (list a b))
                             (invoke (select-function flag) x)
                             (let ((f (select-function flag))) (invoke f x))
                             (invoke-apply (select-function flag) x)
                             (invoke-values (select-function flag) x)
                             (funcall (if flag #'left #'right) x))
                       *selections*))
                    (defun arity-entry (flag x) (funcall (if flag #'left #'pair) x)))"))
         (entry (intern "ENTRY" *package*)) (arity-entry (intern "ARITY-ENTRY" *package*))
         (selections (intern "*SELECTIONS*" *package*))
         (generics (mapcar (lambda (name) (intern name *package*)) '("LEFT" "RIGHT" "PAIR")))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(finite-callable-unions) :closed-generics generics
                :universe '(symbol number) :entries (list entry arity-entry)
                :external-domains (list (list entry '(symbol number)) (list arity-entry '(symbol number)))))
         (flow (getf (snowgrave:unit-report unit) :ordinary-function-flow)))
    (dolist (form forms) (eval form))
    (dolist (flag '(t nil))
      (dolist (argument '(17 1/2 #c(2 3)))
        (setf (symbol-value selections) 0)
        (let ((ordinary (multiple-value-list (funcall entry flag argument))))
          (setf (symbol-value selections) 0)
          (check (equal ordinary (multiple-value-list (funcall (snowgrave:unit-function unit entry) flag argument)))))))
    (check (eq (getf flow :callable-identity-facts) :finite-named-source-target-unions))
    (dolist (name '("INVOKE" "INVOKE-APPLY" "INVOKE-VALUES"))
      (let ((domain (first (getf (find name (getf flow :functions) :test #'string= :key #'proof-name) :required-domains))))
        (check (and (eq (car domain) 'or) (= (length domain) 3)
                    (every (lambda (generic) (member (list :function-target generic) (cdr domain) :test #'equal))
                           (butlast generics))))))
    (let* ((pair (third generics)) (identity '(finite-callable-unions))
           (ordinary-bindings (list (cons (fdefinition pair) (list identity :generic pair))))
           (closed-bindings (list (cons (test-code-function unit pair) (list identity :generic pair)))))
      (dolist (flag '(t nil))
        (check (equal (contract-observation (fdefinition arity-entry) (list flag 17) ordinary-bindings)
                      (contract-observation (snowgrave:unit-function unit arity-entry) (list flag 17) closed-bindings)))))
    (dolist (case '((snowgrave:unclosed-call :computed-function "(invoke (if flag #'left 17) x)")
                    (snowgrave:unclosed-call :computed-function "(invoke (if flag #'left (lambda (x) x)) x)")
                    (snowgrave:incomplete-domain :apply-arguments "(let ((tail nil)) (apply (if flag #'left #'pair) x tail))")))
      (destructuring-bind (type feature body) case
        (let ((condition
                (handler-case
                    (snowgrave:close-source-unit
                     (list :forms (replace-entry-body forms "ENTRY"
                                   `(progn ,(fourth (find entry forms :key #'cadr)) ,(read-from-string body))))
                     :unit-name (list 'rejected-callable-union body) :closed-generics generics
                     :universe '(symbol number) :entries (list entry arity-entry)
                     :external-domains (list (list entry '(symbol number)) (list arity-entry '(symbol number))))
                  (snowgrave:snowgrave-error (condition) condition))))
          (check (typep condition type))
          (check (eq (snowgrave:error-feature condition) feature)))))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-callable-union.lisp" root))
           (metadata (merge-pathnames ".build/fresh-callable-union.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh finite callable union executed."
                     (uiop:run-program
                      (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                            (namestring (merge-pathnames "scripts/fresh-callable-union.lisp" root))
                            (namestring source) (namestring metadata)) :output :string))))))


(defpackage #:snowgrave.callable-union-return.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defgeneric #:defmethod))

(defun callable-union-return-tests ()
  (let* ((*package* (find-package :snowgrave.callable-union-return.fixture))
         (forms (read-from-string
                 "((defgeneric accept (x)) (defmethod accept ((x number)) (list :accepted x))
                    (defun left (x) (+ x 1)) (defun right (x) (- x 1))
                    (defun entry (flag x) (accept (funcall (if flag #'left #'right) x))))"))
         (generic (intern "ACCEPT" *package*)) (entry (intern "ENTRY" *package*))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(finite-callable-return-unions) :closed-generics (list generic)
                :universe '(symbol number) :entries (list entry) :external-domains (list (list entry '(symbol number))))))
    (dolist (form forms) (eval form))
    (dolist (flag '(t nil))
      (dolist (argument '(17 1/2 #c(2 3)))
        (check (equal (multiple-value-list (funcall entry flag argument))
                      (multiple-value-list (funcall (snowgrave:unit-function unit entry) flag argument))))))
    (let ((bad (replace-entry-body forms "RIGHT" (read-from-string "(list x)"))))
      (dolist (form bad) (eval form))
      (signals sb-pcl::no-applicable-method-error (funcall entry nil 17))
      (let ((condition
              (handler-case
                  (snowgrave:close-source-unit
                   (list :forms bad) :unit-name '(incompatible-callable-return-unions) :closed-generics (list generic)
                   :universe '(symbol number) :entries (list entry) :external-domains (list (list entry '(symbol number))))
                (snowgrave:incomplete-domain (condition) condition))))
        (check (typep condition 'snowgrave:incomplete-domain))
        (check (eq (snowgrave:error-feature condition) :internal-call-domain))))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-callable-union-return.lisp" root))
           (metadata (merge-pathnames ".build/fresh-callable-union-return.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh finite callable returns executed."
                     (uiop:run-program
                      (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                            (namestring (merge-pathnames "scripts/fresh-callable-union-return.lisp" root))
                            (namestring source) (namestring metadata)) :output :string))))))

(defun returned-callable-local-name-tests ()
  (let* ((*package* (find-package :snowgrave.callable-union-return.fixture))
         (generic (intern "VALUE" *package*)) (entry (intern "ENTRY" *package*))
         (forms (read-from-string
                 "((defgeneric value (x)) (defmethod value ((x number)) :global-generic)
                    (defun callback () #'value)
                    (defun entry (x) (flet ((value (x) (declare (ignore x)) :lexical-function))
                                      (funcall (callback) x))))"))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(returned-global-target-local-shadow) :closed-generics (list generic)
                :universe '(number) :entries (list entry) :external-domains (list (list entry '(number))))))
    (dolist (form forms) (eval form))
    (check (eq (funcall entry 17) :global-generic))
    (check (eq (funcall (snowgrave:unit-function unit entry) 17) :global-generic))
    (let ((bad (replace-entry-body forms "ENTRY" (read-from-string
               "(flet ((value (x) (declare (ignore x)) :lexical-function)) (funcall (callback) :outside))"))))
      (dolist (form bad) (eval form))
      (signals sb-pcl::no-applicable-method-error (funcall entry 17))
      (let ((condition
              (handler-case
                  (snowgrave:close-source-unit
                   (list :forms bad) :unit-name '(rejected-global-target-local-shadow) :closed-generics (list generic)
                   :universe '(number) :entries (list entry) :external-domains (list (list entry '(number))))
                (snowgrave:incomplete-domain (condition) condition))))
        (check (typep condition 'snowgrave:incomplete-domain))
        (check (eq (snowgrave:error-feature condition) :internal-call-domain))))))

(defpackage #:snowgrave.callable-optional.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defgeneric #:defmethod))

(defun callable-optional-tests ()
  (let* ((*package* (find-package :snowgrave.callable-optional.fixture))
         (forms (read-from-string
                 "((defparameter *defaults* nil)
                    (defgeneric left (x)) (defmethod left ((x number)) (+ x 1))
                    (defgeneric right (x)) (defmethod right ((x number)) (- x 1))
                    (defun default-function () #'left)
                    (defun note-default (tag function) (push tag *defaults*) function)
                    (defun invoke (x &optional (f (note-default :fn (default-function)) fp)
                                              (alias (note-default :alias f) ap))
                      (values (funcall alias x) fp ap))
                    (defun positional-default (f x &optional (alias f)) (funcall alias x))
                    (defun entry (x)
                      (values
                       (list (multiple-value-bind (a fp ap) (invoke x) (list a fp ap))
                             (multiple-value-bind (a fp ap) (invoke x #'right) (list a fp ap))
                             (multiple-value-bind (a fp ap) (invoke x #'right #'left) (list a fp ap))
                             (multiple-value-bind (a fp ap) (let ((tail nil)) (apply #'invoke x #'right #'left tail)) (list a fp ap))
                             (multiple-value-bind (a fp ap) (let ((f #'right)) (invoke x f)) (list a fp ap))
                             (multiple-value-bind (a fp ap) (flet ((default-function () #'right)) (invoke x)) (list a fp ap))
                             (positional-default #'right x))
                       (reverse *defaults*))))"))
         (entry (intern "ENTRY" *package*)) (defaults (intern "*DEFAULTS*" *package*))
         (generics (mapcar (lambda (name) (intern name *package*)) '("LEFT" "RIGHT")))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(optional-callable-bindings) :closed-generics generics
                :universe '(number) :entries (list entry) :external-domains (list (list entry '(number)))))
         (flow (getf (snowgrave:unit-report unit) :ordinary-function-flow)))
    (dolist (form forms) (eval form))
    (dolist (argument '(17 1/2 #c(2 3)))
      (setf (symbol-value defaults) nil)
      (let ((ordinary (multiple-value-list (funcall entry argument))))
        (setf (symbol-value defaults) nil)
        (check (equal ordinary (multiple-value-list (funcall (snowgrave:unit-function unit entry) argument))))))
    (check (eq (getf flow :optional-domain-method) :effective-call-site-bindings))
    (let* ((proof (find "INVOKE" (getf flow :functions) :test #'string= :key #'proof-name))
           (optional (getf proof :optional-domains)))
      (check (equal (getf proof :required-domains) '(number)))
      (check (= (length optional) 2))
      (dolist (domain optional)
        (check (and (eq (car domain) 'or) (= (length domain) 3)
                    (every (lambda (generic) (member (list :function-target generic) (cdr domain) :test #'equal)) generics)))))
    (dolist (body '("(invoke x 17)" "(let ((tail (list #'right))) (apply #'invoke x tail))"))
      (let ((condition
              (handler-case
                  (snowgrave:close-source-unit
                   (list :forms (replace-entry-body forms "ENTRY"
                                 `(progn ,(fourth (find entry forms :key #'cadr)) ,(read-from-string body))))
                   :unit-name (list 'unproved-optional-binding body) :closed-generics generics
                   :universe '(number) :entries (list entry) :external-domains (list (list entry '(number))))
                (snowgrave:unclosed-call (condition) condition))))
        (check (typep condition 'snowgrave:unclosed-call))
        (check (eq (snowgrave:error-feature condition) :computed-function))))
    (signals snowgrave:unclosed-call
      (snowgrave:close-source-unit
       (list :forms (append (subseq forms 0 5)
                           (list (read-from-string "(defun entry (x &optional (f #'left)) (funcall f x))"))))
       :unit-name '(unproved-external-optional-binding) :closed-generics generics
       :universe '(number) :entries (list entry) :external-domains (list (list entry '(number)))))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-callable-optional.lisp" root))
           (metadata (merge-pathnames ".build/fresh-callable-optional.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh optional callable bindings executed."
                     (uiop:run-program
                      (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                            (namestring (merge-pathnames "scripts/fresh-callable-optional.lisp" root))
                            (namestring source) (namestring metadata)) :output :string))))))

(defpackage #:snowgrave.callable-key.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defgeneric #:defmethod))

(defun callable-key-tests ()
  (let* ((*package* (find-package :snowgrave.callable-key.fixture))
         (forms (read-from-string
                 "((defparameter *events* nil)
                    (defgeneric left (x)) (defmethod left ((x number)) (+ x 1))
                    (defgeneric right (x)) (defmethod right ((x number)) (- x 1))
                    (defun default-function () #'left)
                    (defun note-default (tag function) (push tag *events*) function)
                    (defun invoke (x &rest tail &key ((:via f) (note-default :fn (default-function)) fp)
                                                   (alias (note-default :alias f) ap) &allow-other-keys)
                      (values (funcall alias x) fp ap (length tail)))
                    (defun first-only (x &key ((:via f) #'left)) (funcall f x))
                    (defun optional-key (f x &optional (o f) &key ((:via alias) o)) (funcall alias x))
                    (defun named (x &key ((route f) #'left)) (funcall f x))
                    (defun entry (x)
                      (values
                       (list (multiple-value-bind (a fp ap n) (invoke x) (list a fp ap n))
                             (multiple-value-bind (a fp ap n) (invoke x :via #'right) (list a fp ap n))
                             (multiple-value-bind (a fp ap n) (invoke x :via #'right :alias #'left) (list a fp ap n))
                             (multiple-value-bind (a fp ap n) (invoke x :via #'right :via #'left) (list a fp ap n))
                             (multiple-value-bind (a fp ap n) (invoke x :via #'right :via 17) (list a fp ap n))
                             (multiple-value-bind (a fp ap n) (invoke x :via #'left :unused 17 :allow-other-keys t) (list a fp ap n))
                             (multiple-value-bind (a fp ap n) (apply #'invoke x (list :via #'right :alias #'right)) (list a fp ap n))
                             (multiple-value-bind (a fp ap n) (let ((tail nil)) (apply #'invoke x :via #'right :alias #'left tail)) (list a fp ap n))
                             (multiple-value-bind (a fp ap n) (flet ((default-function () #'right)) (invoke x)) (list a fp ap n))
                             (multiple-value-bind (a fp ap n) (invoke x (progn (push :key *events*) :via) #'right) (list a fp ap n))
                             (let ((tail (list :via #'left))) (apply #'first-only x :via #'right tail))
                             (optional-key #'right x)
                             (optional-key #'right x #'left :via #'right)
                             (named x 'route #'right))
                       (reverse *events*))))"))
         (entry (intern "ENTRY" *package*)) (events (intern "*EVENTS*" *package*))
         (generics (mapcar (lambda (name) (intern name *package*)) '("LEFT" "RIGHT")))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(key-callable-bindings) :closed-generics generics
                :universe '(number) :entries (list entry) :external-domains (list (list entry '(number)))))
         (flow (getf (snowgrave:unit-report unit) :ordinary-function-flow)))
    (dolist (form forms) (eval form))
    (dolist (argument '(17 1/2 #c(2 3)))
      (setf (symbol-value events) nil)
      (let ((ordinary (multiple-value-list (funcall entry argument))))
        (setf (symbol-value events) nil)
        (check (equal ordinary (multiple-value-list (funcall (snowgrave:unit-function unit entry) argument))))))
    (check (eq (getf flow :key-domain-method) :first-occurrence-call-site-bindings))
    (let* ((proof (find "INVOKE" (getf flow :functions) :test #'string= :key #'proof-name))
           (keys (getf proof :key-domains)))
      (check (equal (getf proof :required-domains) '(number)))
      (check (null (getf proof :optional-domains)))
      (check (equal (mapcar #'first keys) '(:via :alias)))
      (dolist (key keys)
        (check (and (eq (car (second key)) 'or) (= (length (second key)) 3)
                    (every (lambda (generic) (member (list :function-target generic) (cdr (second key)) :test #'equal)) generics)))))
    ;; First occurrence is authoritative. A later good duplicate cannot repair
    ;; the actual noncallable first binding; execute the ordinary error first.
    (let* ((bad (replace-entry-body forms "ENTRY"
                  `(progn ,(fourth (find entry forms :key #'cadr))
                          ,(read-from-string "(invoke x :via 17 :via #'right)"))))
           (condition nil))
      (dolist (form bad) (eval form))
      (check (handler-case (progn (funcall entry 17) nil) (type-error () t)))
      (setf condition
            (handler-case
                (snowgrave:close-source-unit
                 (list :forms bad) :unit-name '(first-noncallable-key) :closed-generics generics
                 :universe '(number) :entries (list entry) :external-domains (list (list entry '(number))))
              (snowgrave:unclosed-call (condition) condition)))
      (check (typep condition 'snowgrave:unclosed-call))
      (check (eq (snowgrave:error-feature condition) :computed-function)))
    (dolist (body '("(let ((tail (list :via #'right))) (apply #'invoke x tail))"
                   "(let ((key (if (minusp x) :via :alias))) (invoke x key #'right))"))
      (let ((condition
              (handler-case
                  (snowgrave:close-source-unit
                   (list :forms (replace-entry-body forms "ENTRY"
                                 `(progn ,(fourth (find entry forms :key #'cadr)) ,(read-from-string body))))
                   :unit-name (list 'unproved-key-binding body) :closed-generics generics
                   :universe '(number) :entries (list entry) :external-domains (list (list entry '(number))))
                (snowgrave:unclosed-call (condition) condition))))
        (check (typep condition 'snowgrave:unclosed-call))
        (check (eq (snowgrave:error-feature condition) :computed-function))))
    (signals snowgrave:unclosed-call
      (snowgrave:close-source-unit
       (list :forms (append (subseq forms 0 5)
                           (list (read-from-string "(defun entry (x &key (f #'left)) (funcall f x))"))))
       :unit-name '(unproved-external-key-binding) :closed-generics generics
       :universe '(number) :entries (list entry) :external-domains (list (list entry '(number)))))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-callable-key.lisp" root))
           (metadata (merge-pathnames ".build/fresh-callable-key.metadata" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (check (search "Fresh keyword callable bindings executed."
                     (uiop:run-program
                      (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                            (namestring (merge-pathnames "scripts/fresh-callable-key.lisp" root))
                            (namestring source) (namestring metadata)) :output :string))))))

(defun destructuring-shadow-tests ()
  (let* ((*package* (find-package :snowgrave.destructuring.fixture))
         (generic (intern "LOCAL-CALL" *package*))
         (entry (intern "ENTRY" *package*))
         (forms (read-from-string
                 "((defgeneric local-call (x))
                    (defmethod local-call ((x t)) (list :closed x))
                    (defun entry (x)
                      (let ((d #'local-call))
                        (destructuring-bind ((c d)) (list (list 1 (snowgrave.tests::provide-foreign-callable)))
                          (declare (ignore c)) (funcall d x)))))")))
    (dolist (form forms) (eval form))
    (let ((*mutable-foreign-invoked* nil))
      (check (equal (funcall entry 7) '(:foreign 7)))
      (check *mutable-foreign-invoked*))
    (labels ((close-it (identity forms)
               (snowgrave:close-source-unit
                (list :forms forms) :unit-name identity :universe '(t)
                :closed-generics (list generic) :entries (list entry) :external-domains (list (list entry '(t)))
                ;; Without explicit compiler-helper admission, compiled audit
                ;; accidentally masks the unsound source-level callable proof.
                :external-operations '(provide-foreign-callable sb-c::check-ds-list))))
      (let ((condition (handler-case (close-it '(nested-destructuring-callback) forms)
                         (snowgrave:unclosed-call (condition) condition))))
        (check (typep condition 'snowgrave:unclosed-call))
        (check (eq (snowgrave:error-feature condition) :computed-function)))
      (signals snowgrave:unclosed-call
        (close-it '(deep-nested-destructuring-callback)
                  (replace-entry-body forms "ENTRY"
                                      (read-from-string "(let ((d #'local-call)) (destructuring-bind ((c (d))) (list (list 1 (list (snowgrave.tests::provide-foreign-callable)))) (declare (ignore c)) (apply d (list x))))"))))
      (let* ((unit (close-it '(nested-destructuring-independent-capture)
                            (replace-entry-body forms "ENTRY"
                                                (read-from-string "(let ((f #'local-call)) (destructuring-bind ((c d)) (list (list 1 (snowgrave.tests::provide-foreign-callable))) (declare (ignore c d)) (funcall f x)))"))))
             (*mutable-foreign-invoked* nil))
        (check (equal (funcall (snowgrave:unit-function unit entry) 7) '(:closed 7)))
        (check (not *mutable-foreign-invoked*))))
    (check (equal (snowgrave:source-required-binding-variables '(a (b (c d)) () e) :nested t) '(a b c d e)))
    (let ((cyclic (list nil)))
      (setf (car cyclic) cyclic)
      (signals snowgrave:unsupported-definition (snowgrave:source-required-binding-variables cyclic :nested t)))
    (signals snowgrave:unsupported-definition (snowgrave:source-required-binding-variables '((a b))))
    (signals snowgrave:unsupported-definition (snowgrave:source-required-binding-variables '((a &rest b)) :nested t))))

(defpackage #:snowgrave.multiple-value-binding.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass #:defgeneric #:defmethod))

(defun multiple-value-binding-tests ()
  (let* ((*package* (find-package :snowgrave.multiple-value-binding.fixture))
         (class (intern "NODE")) (generic (intern "AMOUNT")) (trace (intern "*TRACE*"))
         (prefix (read-from-string
                  "((defclass node () ((payload :initarg :payload)))
                     (defparameter *trace* nil)
                     (defgeneric amount (r n))
                     (defmethod amount ((r node) (n number))
                       (multiple-value-bind (tag object missing) (method-pack r)
                         (values (+ n (slot-value object 'payload)) missing tag)))
                     (defun method-pack (r) (values :method r))
                     (defun relay (r) (pack r))
                     (defun pack (r) (values :tuple r #'amount))
                     (defun escape-pack (r) (return-from escape-pack (relay r)))
                     (defun recursive-pack (r n)
                       (if (zerop n) (relay r) (recursive-pack r (1- n))))
                     (defun optional-pack (r &optional (function #'amount supplied))
                       (values r function supplied))
                     (defun key-pack (r &key (via #'amount supplied))
                       (values r via supplied))
                     (defun default-escape-pack (r &optional (via #'amount supplied))
                       (if supplied (values :provided r via)
                           (return-from default-escape-pack (values :escape r via))))
                     (defun zero-pack () (values))
                     (defun variable-primary (r n)
                       (if (plusp n) (values r :present) (values r)))
                     (defun variable-callable (n)
                       (if (plusp n) (values #'amount :present) (values #'amount)))
                     (defun variable-pack (r n)
                       (if (plusp n) (values :variable r #'amount :extra) (values :variable r #'amount)))
                     (defun escaped-variable-pack (r n)
                       (if (plusp n) (return-from escaped-variable-pack (values :escape r #'amount))
                           (values :escape r #'amount :extra)))
                     (defun recursive-variable-pack (r n remaining)
                       (if (zerop remaining) (variable-pack r n) (recursive-variable-pack r n (1- remaining))))
                     (defun argument-pack (r n) (push :tuple *trace*) (values r n))
                     (defun comparison-pack (r n)
                       (values r (if (plusp n) r (make-instance 'node :payload (slot-value r 'payload)))))
                     (defun key-arguments (r) (values r :via #'amount :via #'amount))
                     (defun via-values (r) (multiple-value-call #'pack (values r)))
                     (defun project (r)
                       (multiple-value-bind (tag value) (values :tag r) (declare (ignore tag)) value))
                     (defun escape-project (r)
                       (multiple-value-bind (tag value) (values :tag r)
                         (declare (ignore tag)) (return-from escape-project value)))
                     (defun callback ()
                       (multiple-value-bind (tag function) (values :tag #'amount)
                         (declare (ignore tag)) function))
                     (defun boot (n) (make-instance 'node :payload n)))"))
         (bodies
           '("(multiple-value-bind (tag object missing) (values :tag r) (values (slot-value object 'payload) tag missing))"
             "(multiple-value-bind (tag function) (values :tag #'amount) (declare (ignore tag)) (funcall function r n))"
             "(values (slot-value (project r) 'payload) (eq (project r) r))"
             "(funcall (callback) r n)"
             "(multiple-value-bind (x) (values (progn (push :first *trace*) n) (progn (push :ignored *trace*) r) (progn (push :extra *trace*) #'amount)) (values x (reverse *trace*)))"
             "(let ((function #'amount)) (multiple-value-bind (function object) (values function r) (funcall function object n)))"
             "(multiple-value-bind (a b c) (values) (values a b c))"
             "(values (slot-value (escape-project r) 'payload) (eq (escape-project r) r))"
             "(multiple-value-bind (object) (values r) (unwind-protect (values (slot-value object 'payload) :tag nil) (push :cleanup *trace*)))"
             "(let ((object r)) (multiple-value-bind (object function) (values object (if (plusp n) #'amount #'amount)) (funcall function object n)))"
             "(multiple-value-bind (tag object function missing) (relay r) (values (funcall function object n) tag missing))"
             "(multiple-value-bind (tag object function) (funcall #'relay r) (values (funcall function object n) tag))"
             "(multiple-value-bind (tag object function) (apply #'relay (list r)) (values (funcall function object n) tag))"
             "(multiple-value-bind (tag object function) (escape-pack r) (values (funcall function object n) tag))"
             "(multiple-value-bind (tag object function) (recursive-pack r (abs n)) (values (funcall function object n) tag))"
             "(multiple-value-bind (object function supplied) (optional-pack r) (values (funcall function object n) supplied))"
             "(multiple-value-bind (object function supplied) (optional-pack r #'amount) (values (funcall function object n) supplied))"
             "(multiple-value-bind (object function supplied) (key-pack r :via #'amount :via #'amount) (values (funcall function object n) supplied))"
             "(multiple-value-bind (tag object function) (default-escape-pack r) (values (funcall function object n) tag))"
             "(multiple-value-bind (tag object function) (default-escape-pack r #'amount) (values (funcall function object n) tag))"
             "(multiple-value-bind (a b c) (zero-pack) (values a b c))"
             "(multiple-value-bind (tag object function) (unwind-protect (relay r) (push :producer-cleanup *trace*)) (values (funcall function object n) tag (reverse *trace*)))"
             "(multiple-value-bind (tag object function) (multiple-value-prog1 (relay r) (push :producer-after *trace*)) (values (funcall function object n) tag (reverse *trace*)))"
             "(multiple-value-bind (tag object function) (let ((object r)) (if (plusp n) (relay object) (pack object))) (values (funcall function object n) tag))"
             "(multiple-value-bind (object missing) (boot n) (values (slot-value object 'payload) missing))"
             "(multiple-value-bind (object missing) (funcall #'boot n) (values (funcall #'amount object n) missing))"
             "(multiple-value-bind (object missing) (apply #'boot (list n)) (values (funcall #'amount object n) missing))"
             "(multiple-value-bind (object tag) (variable-primary r n) (values (slot-value object 'payload) tag))"
             "(multiple-value-bind (function tag) (variable-callable n) (values (funcall function r n) tag))"
             "(multiple-value-bind (object tag) (if (plusp n) (values r :present) (values r)) (values (slot-value object 'payload) tag))"
             "(multiple-value-bind (object tag) (unwind-protect (variable-primary r n) (push :partial-cleanup *trace*)) (values (slot-value object 'payload) tag (reverse *trace*)))"
             "(multiple-value-bind (string missing) (reverse \"Abc\") (values string missing))"
             "(multiple-value-call #'amount (argument-pack r n))"
             "(multiple-value-call (progn (push :callee *trace*) #'amount) (progn (push :zero *trace*) (zero-pack)) (argument-pack r n))"
             "(multiple-value-call #'amount (progn (push :record *trace*) (values r)) (progn (push :number *trace*) n) (zero-pack))"
             "(multiple-value-bind (object function supplied) (multiple-value-call #'optional-pack (progn (push :input *trace*) (values r))) (values (funcall function object n) supplied))"
             "(multiple-value-bind (object function supplied) (multiple-value-call #'key-pack (key-arguments r)) (values (funcall function object n) supplied))"
             "(multiple-value-bind (tag object function) (via-values r) (values (funcall function object n) tag))"
             "(multiple-value-call #'equalp (comparison-pack r n))"
             "(multiple-value-call (progn (push :callee *trace*) (if (plusp n) #'eq #'equalp)) (comparison-pack r n))"
             "(multiple-value-call #'mapcar (zero-pack) (values #'equalp (list r r) (list r (make-instance 'node :payload 17))))"
             "(not (multiple-value-call #'find (zero-pack) (values r (list (make-instance 'node :payload 17)) :test #'equalp)))"
             "(unwind-protect (multiple-value-call #'amount (argument-pack r n)) (push :mvc-cleanup *trace*))"
             "(multiple-value-bind (tag object function extra) (variable-pack r n) (values (slot-value object 'payload) (funcall function object n) tag extra))"
             "(multiple-value-bind (tag object function extra) (funcall #'variable-pack r n) (values (funcall function object n) tag extra))"
             "(multiple-value-bind (tag object function extra) (apply #'variable-pack (list r n)) (values (funcall function object n) tag extra))"
             "(multiple-value-bind (tag object function extra) (escaped-variable-pack r n) (values (funcall function object n) tag extra))"
             "(multiple-value-bind (tag object function extra) (recursive-variable-pack r n (abs n)) (values (funcall function object n) tag extra))"
             "(multiple-value-bind (tag object function extra) (if (plusp n) (values :branch r #'amount) (values :branch r #'amount :extra)) (values (funcall function object n) tag extra))"))
         (entries (loop for body in bodies for i from 0
                        collect (intern (format nil "ENTRY-~D" i))))
         (forms (append prefix (loop for entry in entries for body in bodies
                                   collect `(defun ,entry (,(intern "R") ,(intern "N")) ,(read-from-string body)))))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(multiple-value-bind-explicit-values)
                :closed-classes (list class) :closed-generics (list generic) :universe (list class 'number)
                :entries (cons (intern "BOOT") entries)
                :external-domains (cons (list (intern "BOOT") '(number))
                                        (mapcar (lambda (entry) (list entry (list class 'number))) entries))))
         (record (funcall (snowgrave:unit-function unit (intern "BOOT")) 17))
         (expected nil))
    (dolist (form forms) (eval form))
    (let ((native (make-instance class :payload 17)))
      (dolist (entry entries)
        (let ((cases nil))
          (dolist (n '(3 -2))
            (setf (symbol-value trace) nil)
            (let ((values (multiple-value-list (funcall entry native n)))
                  (effects (reverse (symbol-value trace))))
              (setf (symbol-value trace) nil)
              (check (equal values (multiple-value-list (funcall (snowgrave:unit-function unit entry) record n))))
              (check (equal effects (reverse (symbol-value trace))))
              (push (list n values effects) cases)))
          (push (nreverse cases) expected))))
    (setf expected (nreverse expected))
    (check (equal (second (first (first expected))) '(17 :tag nil)))
    (check (equal (second (first (second expected))) '(20 nil :method)))
    (let* ((proofs (getf (getf (snowgrave:unit-metadata unit) :ordinary-function-flow) :functions))
           (pack (find "PACK" proofs :key #'proof-name :test #'equal))
           (zero (find "ZERO-PACK" proofs :key #'proof-name :test #'equal))
           (partial (find "VARIABLE-PRIMARY" proofs :key #'proof-name :test #'equal))
           (via (find "VIA-VALUES" proofs :key #'proof-name :test #'equal))
           (variable (find "VARIABLE-PACK" proofs :key #'proof-name :test #'equal)))
      (check (getf pack :returned-value-count-complete-p))
      (check (equal (getf pack :returned-value-domains)
                    (list '(eql :tuple) class (list :function-target generic))))
      (check (getf zero :returned-value-count-complete-p))
      (check (and (null (getf zero :returned-value-domains))
                  (equal (getf zero :primary-return-domain) '(eql nil))))
      (check (not (getf partial :returned-value-count-complete-p)))
      (check (and (null (getf partial :returned-value-domains))
                  (equal (getf partial :primary-return-domain) class)))
      (check (getf via :returned-value-count-complete-p))
      (check (equal (getf via :returned-value-domains) (getf pack :returned-value-domains)))
      (check (and (not (getf variable :returned-value-count-complete-p))
                  (null (getf variable :returned-value-domains))))
      (check (equal (getf variable :primary-return-domain) '(eql :variable))))
    ;; Unproved secondary producer/foreign target, mutation and lexical
    ;; shadow cases remain rejected. A known primary is not a complete tuple.
    (labels ((refused (body &optional externals)
               (let* ((entry (car entries))
                      (changed (append prefix (list `(defun ,entry (,(intern "R") ,(intern "N"))
                                                      ,(read-from-string body))))))
                 (signals snowgrave:snowgrave-error
                   (snowgrave:close-source-unit
                    (list :forms changed) :unit-name (list :refused-secondary-binding body)
                    :closed-classes (list class) :closed-generics (list generic) :universe (list class 'number)
                    :entries (list entry) :external-domains (list (list entry (list class 'number)))
                    :external-operations externals)))))
      (refused "(multiple-value-bind (tag object) (amount r n) (declare (ignore tag)) (slot-value object 'payload))")
      (refused "(let ((function #'amount)) (multiple-value-bind (tag function) (values :tag (snowgrave.tests::provide-foreign-callable)) (declare (ignore tag)) (funcall function r n)))"
               '(provide-foreign-callable))
      (refused "(multiple-value-bind (object) (values r) (setq object n) (slot-value object 'payload))")
      (refused "(multiple-value-bind (function) (values #'amount) (declare (special function)) (funcall function r n))")
      (refused "(multiple-value-bind (object object) (values r n) (slot-value object 'payload))")
      (refused "(multiple-value-bind (object function) (if (plusp n) (values r #'amount) (values r)) (funcall function object n))")
      (refused "(flet ((relay (x) (declare (ignore x)) (values :foreign n (snowgrave.tests::provide-foreign-callable)))) (multiple-value-bind (tag object function) (relay r) (declare (ignore tag)) (funcall function object n)))"
               '(provide-foreign-callable))
      (refused "(multiple-value-bind (tag object function) (unwind-protect (relay r) (setq r n)) (declare (ignore tag)) (funcall function object n))")
      (refused "(multiple-value-bind (object tag) (if (plusp n) (values r) (values)) (declare (ignore tag)) (slot-value object 'payload))")
      (refused "(multiple-value-bind (function tag) (if (plusp n) (values #'amount) (values)) (declare (ignore tag)) (funcall function r n))")
      (refused "(let ((function #'amount)) (multiple-value-bind (object function) (variable-primary r n) (funcall function object n)))")
      (refused "(multiple-value-call #'amount (variable-primary r n))")
      (refused "(multiple-value-call #'amount (boot n) (values n))")
      ;; A complete lexical tuple proves the reversed argument order, including
      ;; its ordinary MOP miss. Compare the condition, not just acceptance.
      (let* ((entry (intern "LOCAL-REORDERED-MISS"))
             (changed (append prefix
                              (list `(defun ,entry (,(intern "R") ,(intern "N"))
                                       ,(read-from-string
                                         "(flet ((argument-pack (object number) (values number object))) (multiple-value-call #'amount (argument-pack r n)))")))))
             (miss-unit (snowgrave:close-source-unit
                         (list :forms changed) :unit-name '(local-multiple-value-reordered-miss)
                         :closed-classes (list class) :closed-generics (list generic)
                         :universe (list class 'number) :entries (list (intern "BOOT") entry)
                         :external-domains (list (list (intern "BOOT") '(number))
                                                 (list entry (list class 'number)))))
             (miss-record (funcall (snowgrave:unit-function miss-unit (intern "BOOT")) 17)))
        (unwind-protect
             (progn
               (dolist (form changed) (eval form))
               (let ((native (make-instance class :payload 17))
                     (closed-generic (test-code-function miss-unit generic)))
                 (dolist (n '(3 -2))
                   (let ((observation
                           (contract-observation entry (list native n)
                                                 (list (cons native :record)
                                                       (cons (fdefinition generic) :amount)))))
                     (check (eq (first observation) :condition))
                     (check (eq (second observation) 'sb-pcl::no-applicable-method-error))
                     (check (equal observation
                                   (contract-observation
                                    (snowgrave:unit-function miss-unit entry) (list miss-record n)
                                    (list (cons miss-record :record)
                                          (cons closed-generic :amount)))))))))
          ;; Keep the original native fixture aligned with its artifact below.
          (dolist (form forms) (eval form))))
      (refused "(multiple-value-call #'amount (unwind-protect (argument-pack r n) (setq r n)))")
      (refused "(multiple-value-bind (tag object function) (if (plusp n) (values :tag r #'amount) (values :tag r)) (declare (ignore tag)) (funcall function object n))")
      (refused "(multiple-value-bind (tag object) (if (plusp n) (values :tag r) (values :tag n :extra)) (declare (ignore tag)) (slot-value object 'payload))"))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-multiple-value-binding.lisp" root))
           (metadata (merge-pathnames ".build/fresh-multiple-value-binding.metadata" root))
           (observations (merge-pathnames ".build/fresh-multiple-value-binding.expected" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (with-open-file (stream observations :direction :output :if-exists :supersede) (write expected :stream stream :readably t))
      (check (search "Fresh explicit secondary bindings executed."
                     (uiop:run-program
                      (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                            (namestring (merge-pathnames "scripts/fresh-multiple-value-binding.lisp" root))
                            (namestring source) (namestring metadata) (namestring observations)) :output :string))))))

(defpackage #:snowgrave.generic-values.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass #:defgeneric #:defmethod))

(defun generic-method-value-tests ()
  (let* ((*package* (find-package :snowgrave.generic-values.fixture))
         (base (intern "BASE")) (leaf (intern "LEAF"))
         (amount (intern "AMOUNT")) (pack (intern "PACK"))
         (vary (intern "VARY")) (empty (intern "EMPTY")) (trace (intern "*TRACE*"))
         (generics (list amount pack vary empty (intern "ARGUMENTS") (intern "LONE")
                         (intern "RECURSIVE-PACK") (list 'setf (intern "RECEIPT"))))
         (prefix (read-from-string
                  "((defclass base () ((payload :initarg :payload))) (defclass leaf (base) ())
                     (defparameter *trace* nil)
                     (defun relay (r) (pack r))
                     (defun method-tuple (r) (push :tuple *trace*) (values :tag r #'amount))
                     (defgeneric amount (r n))
                     (defmethod amount ((r base) (n number)) (values (+ (slot-value r 'payload) n) :amount))
                     (defgeneric pack (r))
                     (defmethod pack :around ((r leaf))
                       (push :around *trace*)
                       (unwind-protect (call-next-method) (push :cleanup *trace*)))
                     (defmethod pack :before ((r base)) (push :before *trace*) (values :ignored :before))
                     (defmethod pack :after ((r base)) (push :after *trace*) (values :ignored r :after :extra))
                     (defmethod pack ((r base)) (push :base *trace*) (method-tuple r))
                     (defmethod pack ((r leaf)) (push :leaf *trace*) (return-from pack (call-next-method)))
                     (defgeneric arguments (r n))
                     (defmethod arguments ((r base) (n number)) (push :arguments *trace*) (values r n))
                     (defgeneric empty (r))
                     (defmethod empty :before ((r base)) (push :empty-before *trace*) :ignored)
                     (defmethod empty ((r base)) (declare (ignore r)) (push :empty *trace*) (values))
                     (defgeneric vary (r n))
                     (defmethod vary ((r base) (n number))
                       (if (plusp n) (values :vary r #'amount :extra) (values :vary r #'amount)))
                     (defgeneric lone (r))
                     (defmethod lone ((r base))
                       (if (next-method-p) (call-next-method) (values :lone r #'amount)))
                     (defgeneric recursive-pack (r n))
                     (defmethod recursive-pack ((r base) (n number))
                       (if (plusp n) (recursive-pack r (1- n)) (values :recursive r #'amount)))
                     (defgeneric (setf receipt) (value r))
                     (defmethod (setf receipt) ((value number) (r base))
                       (push :writer *trace*) (values r #'amount value))
                     (defun boot-base (n) (make-instance 'base :payload n))
                     (defun boot (n) (make-instance 'leaf :payload n)))"))
         (bodies
           '("(multiple-value-bind (tag object callback absent) (pack r) (values (slot-value object 'payload) (funcall callback object n) tag absent))"
             "(multiple-value-bind (tag object callback) (funcall #'pack r) (values (funcall callback object n) tag))"
             "(multiple-value-bind (tag object callback) (apply #'pack (list r)) (values (funcall callback object n) tag))"
             "(multiple-value-bind (tag object callback) (relay r) (values (funcall callback object n) tag))"
             "(multiple-value-bind (tag object callback extra) (vary r n) (values (slot-value object 'payload) (funcall callback object n) tag extra))"
             "(multiple-value-bind (a b c) (empty r) (values a b c))"
             "(multiple-value-call (progn (push :callee *trace*) #'amount) (empty r) (arguments r n))"
             "(multiple-value-bind (tag object callback) (lone r) (values (funcall callback object n) tag))"
             "(multiple-value-bind (tag object callback) (recursive-pack r (abs n)) (values (funcall callback object n) tag))"
             "(multiple-value-bind (object callback value) (funcall #'(setf receipt) n r) (values (funcall callback object n) value))"
             "(multiple-value-bind (tag object callback) (multiple-value-prog1 (pack r) (push :producer-after *trace*)) (values (funcall callback object n) tag))"
             "(multiple-value-bind (tag object callback) (unwind-protect (pack r) (push :producer-cleanup *trace*)) (values (funcall callback object n) tag))"))
         (entries (loop for i below (length bodies) collect (intern (format nil "ENTRY-~D" i))))
         (forms (append prefix (loop for entry in entries for body in bodies
                                   collect `(defun ,entry (,(intern "R") ,(intern "N")) ,(read-from-string body)))))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(generic-method-values)
                :closed-classes (list base leaf) :closed-generics generics :universe (list base leaf 'number)
                :entries (append (list (intern "BOOT") (intern "BOOT-BASE")) entries)
                :external-domains (append (list (list (intern "BOOT") '(number)) (list (intern "BOOT-BASE") '(number)))
                                        (mapcar (lambda (entry) (list entry (list base 'number))) entries))))
         (expected nil))
    (check (eq (getf (snowgrave:unit-report unit) :claim) :semantically-closed))
    (dolist (form forms) (eval form))
    (dolist (class (list base leaf))
      (let* ((native (make-instance class :payload 17))
             (record (if (eq class leaf) (funcall (test-unit-function unit "BOOT") 17)
                         (funcall (test-unit-function unit "BOOT-BASE") 17))))
        (dolist (entry entries)
          (dolist (n '(3 -2))
            (setf (symbol-value trace) nil)
            (let ((values (multiple-value-list (funcall entry native n)))
                  (effects (reverse (symbol-value trace))))
              (setf (symbol-value trace) nil)
              (check (equal values (multiple-value-list (funcall (snowgrave:unit-function unit entry) record n))))
              (check (equal effects (reverse (symbol-value trace))))
              (push (list (symbol-name entry) (symbol-name class) n values effects) expected))))))
    (let* ((flow (getf (snowgrave:unit-report unit) :ordinary-function-flow))
           (proofs (getf flow :generic-returns)))
      (check (eq (getf flow :generic-return-method) :same-emitted-effective-method-proof-tree))
      (flet ((proof (name) (find (snowgrave::function-name-key name) proofs
                                :key (lambda (x) (getf x :generic-key)) :test #'equal)))
        (check (getf (proof pack) :returned-value-count-complete-p))
        (check (equal (getf (proof pack) :returned-value-domains)
                      (list '(eql :tag) base (list :function-target amount))))
        (check (getf (proof empty) :returned-value-count-complete-p))
        (check (and (null (getf (proof empty) :returned-value-domains))
                    (equal (getf (proof empty) :primary-return-domain) '(eql nil))))
        (check (not (getf (proof vary) :returned-value-count-complete-p)))
        (check (null (getf (proof vary) :returned-value-domains)))))
    (labels ((refused (body &optional (additional nil))
               (let ((entry (first entries)))
                 (signals snowgrave:snowgrave-error
                   (snowgrave:close-source-unit
                    (list :forms (append prefix additional
                                        (list `(defun ,entry (,(intern "R") ,(intern "N")) ,(read-from-string body)))))
                    :unit-name (list :unproved-generic-values body)
                    :closed-classes (list base leaf)
                    :closed-generics (append generics (when additional (list (intern "BAD"))))
                    :universe (list base leaf 'number)
                    :entries (list entry) :external-domains (list (list entry (list base 'number))))))))
      (refused "(multiple-value-call #'amount (vary r n))")
      (refused "(multiple-value-bind (object callback) (empty r) (funcall callback object n))")
      ;; The lexical producer proves a numeric receiver, so invoking its
      ;; returned callback has an ordinary no-applicable-method condition.
      (let* ((entry (intern "LOCAL-PACK-NUMERIC-MISS"))
             (changed (append prefix
                              (list `(defun ,entry (,(intern "R") ,(intern "N"))
                                       ,(read-from-string
                                         "(flet ((pack (x) (declare (ignore x)) (values :tag n #'amount))) (multiple-value-bind (tag object callback) (pack r) (declare (ignore tag)) (funcall callback object n)))")))))
             (miss-unit (snowgrave:close-source-unit
                         (list :forms changed) :unit-name '(local-generic-value-numeric-miss)
                         :closed-classes (list base leaf) :closed-generics generics
                         :universe (list base leaf 'number)
                         :entries (list (intern "BOOT-BASE") entry)
                         :external-domains (list (list (intern "BOOT-BASE") '(number))
                                                 (list entry (list base 'number)))))
             (miss-record (funcall (test-unit-function miss-unit "BOOT-BASE") 17)))
        (unwind-protect
             (progn
               (dolist (form changed) (eval form))
               (let ((native (make-instance base :payload 17))
                     (closed-generic (test-code-function miss-unit amount)))
                 (dolist (n '(3 -2))
                   (let ((observation
                           (contract-observation entry (list native n)
                                                 (list (cons native :record)
                                                       (cons (fdefinition amount) :amount)))))
                     (check (eq (first observation) :condition))
                     (check (eq (second observation) 'sb-pcl::no-applicable-method-error))
                     (check (equal observation
                                   (contract-observation
                                    (snowgrave:unit-function miss-unit entry) (list miss-record n)
                                    (list (cons miss-record :record)
                                          (cons closed-generic :amount)))))))))
          ;; Preserve the original native fixture and fresh-artifact data.
          (dolist (form forms) (eval form))))
      (refused "(multiple-value-bind (tag object callback) (bad r n) (declare (ignore tag)) (funcall callback object n))"
               (read-from-string "((defgeneric bad (r n)) (defmethod bad ((r base) (n number)) (if (plusp n) (values :tag r #'amount) (values :tag r))))"))
      (refused "(multiple-value-bind (tag object) (bad r n) (declare (ignore tag)) (slot-value object 'payload))"
               (read-from-string "((defgeneric bad (r n)) (defmethod bad ((r base) (n number)) (if (plusp n) (values :tag r) (values :tag n :extra))))")))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-generic-values.lisp" root))
           (metadata (merge-pathnames ".build/fresh-generic-values.metadata" root))
           (observations (merge-pathnames ".build/fresh-generic-values.expected" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (with-open-file (stream observations :direction :output :if-exists :supersede) (write (nreverse expected) :stream stream :readably t))
      (check (search "Fresh generic method values executed."
                     (uiop:run-program
                      (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                            (namestring (merge-pathnames "scripts/fresh-generic-values.lisp" root))
                            (namestring source) (namestring metadata) (namestring observations)) :output :string))))))

(defpackage #:snowgrave.conditional-values.fixture
  (:use #:cl) (:shadowing-import-from #:snowgrave #:defclass #:defgeneric #:defmethod))

(defun conditional-value-tests ()
  (let* ((*package* (find-package :snowgrave.conditional-values.fixture))
         (record (intern "RECORD")) (pack (intern "PACK")) (amount (intern "AMOUNT"))
         (escape (intern "METHOD-ESCAPE")) (trace (intern "*TRACE*"))
         (case-pack (intern "CASE-PACK")) (case-escape (intern "CASE-METHOD-ESCAPE"))
         (prefix (read-from-string
                   "((defclass record () ((payload :initarg :payload))) (defparameter *trace* nil)
                      (defgeneric amount (r n))
                      (defmethod amount ((r record) (n number))
                        (push :amount *trace*) (values (+ (slot-value r 'payload) n) :amount))
                      (defun choose (r n)
                        (cond ((progn (push :negative-test *trace*) (minusp n))
                               (push :negative *trace*) (values :negative r #'amount))
                              ((progn (push :zero-test *trace*) (zerop n))
                               (push :zero *trace*) (values :zero r #'amount))
                              (t (push :positive *trace*) (values :positive r #'amount))))
                      (defgeneric pack (r n))
                      (defmethod pack ((r record) (n number))
                        (cond ((progn (push :method-test *trace*) (minusp n)) (values :negative r #'amount))
                              (t (values :positive r #'amount))))
                      (defun escape-choose (r n)
                        (cond ((progn (push :escape-test *trace*)
                                      (when (minusp n) (return-from escape-choose (values :escaped r #'amount))) nil)
                               (values :unused r #'amount))
                              (t (values :normal r #'amount))))
                      (defgeneric method-escape (r n))
                      (defmethod method-escape ((r record) (n number))
                        (cond ((progn (push :method-escape-test *trace*)
                                      (when (minusp n) (return-from method-escape (values :escaped r #'amount))) nil)
                               (values :unused r #'amount))
                              (t (values :normal r #'amount))))
                      (defun invoke (tag object callback n) (values (funcall callback object n) tag))
                      (defun zero (n) (cond ((minusp n) (push :zero-negative *trace*) (values))
                                           (t (push :zero-positive *trace*) (values))))
                      (defun pair (r n)
                        (cond ((progn (push :empty-test *trace*) (values)) (values n r))
                              (t (values r n))))
                      (defun case-choose (r n)
                        (case (progn (push :case-selector *trace*) n)
                          ((-2 0) (push :case-small *trace*) (values :small r #'amount))
                          (otherwise (push :case-default *trace*) (values :default r #'amount))))
                      (defgeneric case-pack (r n))
                      (defmethod case-pack ((r record) (n number))
                        (case (progn (push :case-method-selector *trace*) n)
                          ((-2 0) (values :small r #'amount))
                          (t (values :default r #'amount))))
                      (defun case-escape-choose (r n)
                        (case (progn (push :case-escape-selector *trace*)
                                     (when (minusp n) (return-from case-escape-choose (values :escaped r #'amount))) n)
                          ((-2 0) (values :small r #'amount)) (otherwise (values :default r #'amount))))
                      (defgeneric case-method-escape (r n))
                      (defmethod case-method-escape ((r record) (n number))
                        (case (progn (push :case-method-escape-selector *trace*)
                                     (when (minusp n) (return-from case-method-escape (values :escaped r #'amount))) n)
                          ((-2 0) (values :small r #'amount)) (otherwise (values :default r #'amount))))
                      (defun boot () (make-instance 'record :payload 17)))"))
         (bodies
           '("(multiple-value-bind (tag object callback) (choose r n) (values (slot-value object 'payload) (funcall callback object n) tag))"
             "(multiple-value-bind (tag object callback) (pack r n) (values (slot-value object 'payload) (funcall callback object n) tag))"
             "(multiple-value-bind (tag object callback) (funcall #'pack r n) (values (funcall callback object n) tag))"
             "(multiple-value-bind (tag object callback) (apply #'pack (list r n)) (values (funcall callback object n) tag))"
             "(multiple-value-bind (tag object callback) (cond ((minusp n) (values :negative r #'amount)) (t (values :positive r #'amount))) (values (funcall callback object n) tag))"
             "(multiple-value-bind (object callback tag) (when t (values r #'amount :when)) (values (slot-value object 'payload) (funcall callback object n) tag))"
             "(multiple-value-bind (object callback tag) (unless nil (values r #'amount :unless)) (values (funcall callback object n) tag))"
             "(multiple-value-bind (object callback tag) (and (progn (push :and-test *trace*) t) (values r #'amount :and)) (values (funcall callback object n) tag))"
             "(multiple-value-bind (object callback tag) (or (progn (push :or-test *trace*) nil) (values r #'amount :or)) (values (funcall callback object n) tag))"
             "(multiple-value-bind (a b c) (or (values :tag r #'amount) (values :unused r #'amount)) (values a b c))"
             "(multiple-value-bind (a b c) (cond ((values :tag r #'amount))) (values a b c))"
             "(multiple-value-bind (object callback tag) (cond ((values r #'amount))) (values (eq object r) callback tag))"
             "(multiple-value-bind (object callback tag) (when (minusp n) (values r #'amount :when)) (values (eq object r) (eq callback #'amount) tag))"
             "(multiple-value-bind (object callback tag) (unless (minusp n) (values r #'amount :unless)) (values (eq object r) (eq callback #'amount) tag))"
             "(multiple-value-bind (object callback tag) (and (minusp n) (values r #'amount :and)) (values (eq object r) (eq callback #'amount) tag))"
             "(multiple-value-bind (object callback tag) (or (minusp n) (values r #'amount :or)) (values (eq object r) (eq callback #'amount) tag))"
             "(multiple-value-bind (a b) (and) (multiple-value-bind (c d) (or) (multiple-value-bind (e f) (cond) (values a b c d e f))))"
             "(multiple-value-bind (a b c) (cond ((values nil r #'amount) :unreachable) (t)) (values a b c))"
             "(multiple-value-call #'amount (zero n) (pair r n))"
             "(multiple-value-call #'invoke (choose r n) (values n))"
             "(multiple-value-bind (tag object callback) (escape-choose r n) (values (slot-value object 'payload) (funcall callback object n) tag))"
             "(multiple-value-bind (tag object callback) (method-escape r n) (values (funcall callback object n) tag))"
             "(multiple-value-bind (object callback) (cond ((progn (push :empty-test *trace*) (values)) (values n n)) (t (values r #'amount))) (values (funcall callback object n)))"
             "(multiple-value-bind (a b c) (and (progn (push :false-test *trace*) nil) (values :unreachable r #'amount)) (values a b c))"
             "(cond ((minusp n) (values)) (t (values)))"
             "(cond ((progn (push :slot-test *trace*) (plusp (slot-value r 'payload))) (multiple-value-bind (tag object callback) (choose r n) (values (funcall callback object n) tag))) (t :unused))"
             "(multiple-value-bind (tag object callback) (case-choose r n) (values (slot-value object 'payload) (funcall callback object n) tag))"
             "(multiple-value-bind (tag object callback) (case-pack r n) (values (slot-value object 'payload) (funcall callback object n) tag))"
             "(multiple-value-bind (tag object callback) (funcall #'case-pack r n) (values (funcall callback object n) tag))"
             "(multiple-value-bind (tag object callback) (apply #'case-pack (list r n)) (values (funcall callback object n) tag))"
             "(multiple-value-bind (object callback) (case n ((-2 0) (values r #'amount)) (otherwise (values r #'amount))) (values (slot-value object 'payload) (funcall callback object n)))"
             "(multiple-value-call #'invoke (case-choose r n) (values n))"
             "(multiple-value-call #'invoke (case-pack r n) (values n))"
             "(multiple-value-bind (object callback) (case :ready (:ready (values r #'amount)) (otherwise (values n n))) (values (slot-value object 'payload) (funcall callback object n)))"
             "(multiple-value-call #'amount (case '-2 ((-2 0) (values r n)) (otherwise (values :unused))))"
             "(multiple-value-call #'amount (case (progn (push :constant-selector *trace*) :ready) (:ready (values r n)) (otherwise (values :unused))))"
             "(multiple-value-bind (object callback) (case n (nil (values n n)) (otherwise (values r #'amount))) (values (funcall callback object n)))"
             "(multiple-value-bind (object callback) (case nil ((nil) (values r #'amount)) (otherwise (values n n))) (values (funcall callback object n)))"
             "(multiple-value-bind (object callback) (case t ((t) (values r #'amount)) (otherwise (values n n))) (values (funcall callback object n)))"
             "(multiple-value-bind (object callback) (case 'otherwise ((otherwise) (values r #'amount)) (t (values n n))) (values (funcall callback object n)))"
             "(case n ((-2 0) (values)) (otherwise (values)))"
             "(multiple-value-bind (object callback) (case n ((-2 0) (values r)) (otherwise (values r #'amount))) (values (eq object r) (eq callback #'amount)))"
             "(multiple-value-bind (object callback) (case n ((-2 0) (values r #'amount))) (values (eq object r) (eq callback #'amount)))"
             "(multiple-value-bind (object callback) (case (values n r #'amount) ((-2 0) (values r #'amount)) (otherwise (values r #'amount))) (values (funcall callback object n)))"
             "(multiple-value-bind (tag object callback) (case-escape-choose r n) (values (slot-value object 'payload) (funcall callback object n) tag))"
             "(multiple-value-bind (tag object callback) (case-method-escape r n) (values (funcall callback object n) tag))"
             "(multiple-value-bind (object callback) (case (progn (push :case-slot-selector *trace*) (slot-value r 'payload)) (17 (values r #'amount)) (otherwise (values r #'amount))) (values (funcall callback object n)))"
             "(multiple-value-bind (object callback) (case 'return-from (return-from (values r #'amount)) (otherwise (values n n))) (values (funcall callback object n)))"
             "(multiple-value-bind (a b c d) (case n) (values a b c d))"
             "(multiple-value-bind (a b c d) (case :missing (nil (values :unreachable))) (values a b c d))"))
         (entries (loop for i below (length bodies) collect (intern (format nil "ENTRY-~D" i))))
         (forms (append prefix (loop for entry in entries for body in bodies
                                   collect `(defun ,entry (,(intern "R") ,(intern "N")) ,(read-from-string body)))))
         (unit (snowgrave:close-source-unit (list :forms forms) :unit-name '(conditional-values)
                 :closed-classes (list record) :closed-generics (list pack amount escape case-pack case-escape) :universe (list record 'number)
                 :entries (cons (intern "BOOT") entries)
                 :external-domains (cons (list (intern "BOOT") nil)
                                         (mapcar (lambda (entry) (list entry (list record 'number))) entries))))
         (expected nil))
    (check (eq (getf (snowgrave:unit-report unit) :claim) :semantically-closed))
    (dolist (form forms) (eval form))
    (let ((native (funcall (intern "BOOT"))) (closed (funcall (test-unit-function unit "BOOT"))))
      (dolist (entry entries)
        (dolist (n '(-2 0 7))
          (setf (symbol-value trace) nil)
          (let ((values (multiple-value-list (funcall entry native n))) (effects (reverse (symbol-value trace))))
            (setf (symbol-value trace) nil)
            (check (equal values (multiple-value-list (funcall (snowgrave:unit-function unit entry) closed n))))
            (check (equal effects (reverse (symbol-value trace))))
            (push (list (symbol-name entry) n values effects) expected)))))
    (labels ((refused (bad &optional additional)
               (let ((entry (first entries)))
                 (signals snowgrave:snowgrave-error
                   (snowgrave:close-source-unit
                    (list :forms (append prefix additional (list `(defun ,entry (,(intern "R") ,(intern "N")) ,(read-from-string bad)))))
                    :unit-name (list :unproved-conditional bad) :closed-classes (list record)
                    :closed-generics (list pack amount escape case-pack case-escape) :universe (list record 'number)
                    :entries (list entry) :external-domains (list (list entry (list record 'number))))))))
      (refused "(multiple-value-bind (object callback) (cond ((minusp n) (values r #'amount))) (funcall callback object n))")
      (refused "(multiple-value-call #'amount (when (minusp n) (values r n)))")
      (refused "(multiple-value-bind (object callback) (or (values :tag r #'amount) (values r #'amount)) (funcall callback object n))")
      (refused "(multiple-value-bind (object callback) (bad-escape r n) (values (slot-value object 'payload) (funcall callback object n)))"
               (read-from-string "((defun bad-escape (r n) (cond ((progn (when (minusp n) (return-from bad-escape (values n #'amount))) nil) (values r #'amount)) (t (values r #'amount)))))"))
      (refused "(cond nil)")
      (refused "(cond (t . :bad))")
      (refused "(multiple-value-bind (object callback) (case n ((-2 0) (values r #'amount))) (funcall callback object n))")
      (refused "(multiple-value-call #'amount (case n ((-2 0) (values r n)) (otherwise (values r))))")
      (refused "(multiple-value-bind (object callback) (bad-case-escape r n) (values (slot-value object 'payload) (funcall callback object n)))"
               (read-from-string "((defun bad-case-escape (r n) (case (progn (when (minusp n) (return-from bad-case-escape (values n #'amount))) n) ((-2 0) (values r #'amount)) (otherwise (values r #'amount)))))"))
      (refused "(case)")
      (refused "(case n nil)")
      (refused "(case n (1 . :bad))")
      (refused "(case n ((1 . 2) (values r #'amount)))")
      (refused "(case n (otherwise (values r #'amount)) (1 (values r #'amount)))"))
    (let* ((root (asdf:system-source-directory "snowgrave"))
           (source (merge-pathnames ".build/fresh-conditional-values.lisp" root))
           (metadata (merge-pathnames ".build/fresh-conditional-values.metadata" root))
           (observations (merge-pathnames ".build/fresh-conditional-values.expected" root)))
      (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
      (with-open-file (stream metadata :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
      (with-open-file (stream observations :direction :output :if-exists :supersede) (write (nreverse expected) :stream stream :readably t))
      (check (search "Fresh conditional values executed."
                     (uiop:run-program
                      (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                            (namestring (merge-pathnames "scripts/fresh-conditional-values.lisp" root))
                            (namestring source) (namestring metadata) (namestring observations)) :output :string))))))

(defun multiple-value-closure-tests ()
  (let* ((*package* (find-package :snowgrave.destructuring.fixture))
         (generic (intern "LOCAL-CALL" *package*))
         (entry (intern "ENTRY" *package*))
         (forms (read-from-string
                 "((defgeneric local-call (x))
                    (defmethod local-call ((x t)) (list :closed x))
                    (defun entry (x)
                      (let ((f #'local-call))
                        (multiple-value-setq (f) (snowgrave.tests::provide-foreign-callable))
                        (funcall f x))))")))
    (labels ((close-it (identity forms domains &optional (externals '(provide-foreign-callable)) (closed-generic generic))
               (snowgrave:close-source-unit
                (list :forms forms) :unit-name identity :universe '(t)
                :closed-generics (list closed-generic) :entries (list entry)
                :external-domains (list (list entry domains)) :external-operations externals)))
      (dolist (form forms) (eval form))
      (let ((*mutable-foreign-invoked* nil))
        (check (equal (funcall entry 7) '(:foreign 7)))
        (check *mutable-foreign-invoked*))
      (let ((condition (handler-case (close-it '(mvsetq-capture-mutation) forms '(t))
                         (snowgrave:unclosed-call (condition) condition))))
        ;; Mutation clears the old callee fact; the consuming call must still
        ;; refuse an unproved foreign function rather than reuse LOCAL-CALL.
        (check (typep condition 'snowgrave:unclosed-call))
        (check (eq (snowgrave:error-feature condition) :computed-function)))
      (let ((changed (replace-entry-body forms "ENTRY"
                                        (read-from-string "(let ((f #'local-call)) (multiple-value-setq (x f) (values x (snowgrave.tests::provide-foreign-callable))) (funcall f x))"))))
        (let ((condition (handler-case (close-it '(mvsetq-secondary-mutation) changed '(t))
                           (snowgrave:unclosed-call (condition) condition))))
          (check (typep condition 'snowgrave:unclosed-call))
          (check (eq (snowgrave:error-feature condition) :computed-function))))
      (let ((computed (append (butlast forms)
                              (read-from-string "((defun entry (f x) (multiple-value-call f (values x))))"))))
        (dolist (form computed) (eval form))
        (let ((*mutable-foreign-invoked* nil))
          (check (equal (funcall entry #'mutable-foreign-function 7) '(:foreign 7)))
          (check *mutable-foreign-invoked*))
        (let ((condition (handler-case (close-it '(mvcall-unlisted-callee) computed '(t t) nil)
                           (snowgrave:unclosed-call (condition) condition))))
          (check (typep condition 'snowgrave:unclosed-call))
          (check (eq (snowgrave:error-feature condition) :computed-function))))
      (let* ((ordered (read-from-string
                       "((defparameter *mv-trace* nil)
                          (defgeneric local-pair (x y))
                          (defmethod local-pair ((x t) (y t)) (values (list x y) (reverse *mv-trace*)))
                          (defun entry (x)
                            (multiple-value-call #'local-pair
                              (values (progn (push :first *mv-trace*) x))
                              (values)
                              (values (progn (push :second *mv-trace*) 2)))))"))
             (trace (intern "*MV-TRACE*" *package*))
             (pair (intern "LOCAL-PAIR" *package*)))
        (dolist (form ordered) (eval form))
        (setf (symbol-value trace) nil)
        (let* ((native (multiple-value-list (funcall entry 7)))
               (unit (close-it '(mvcall-ordered-values) ordered '(t) nil pair)))
          (setf (symbol-value trace) nil)
          (check (equal native '((7 2) (:first :second))))
          (check (equal native (multiple-value-list (funcall (snowgrave:unit-function unit entry) 7)))))
        (let* ((proved (append (butlast ordered)
                                (read-from-string "((defun producer (x) (values x 2)) (defun entry (x) (multiple-value-call #'local-pair (producer x))))")))
               (unit (close-it '(mvcall-proved-helper-values) proved '(t) nil pair)))
          (dolist (form proved) (eval form))
          (setf (symbol-value trace) nil)
          (let ((native (multiple-value-list (funcall entry 7))))
            (check (equal native '((7 2) nil)))
            (setf (symbol-value trace) nil)
            (check (equal native (multiple-value-list (funcall (snowgrave:unit-function unit entry) 7))))))
        (dolist (arguments '(nil (x) (x 2 :extra)))
          (let* ((producer (intern "PRODUCER" *package*))
                 (inputs (substitute (intern "X" *package*) 'x arguments))
                 (changed (append (butlast ordered)
                                  (list `(defun ,producer (,(intern "X" *package*))
                                           (push :producer ,trace) (values ,@inputs))
                                        `(defun ,entry (,(intern "X" *package*))
                                           (multiple-value-call #',pair (,producer ,(intern "X" *package*)))))))
                 (unit (close-it (list 'mvcall-helper-arity arguments) changed '(t) nil pair)))
            (dolist (form changed) (eval form))
            (setf (symbol-value trace) nil)
            (let ((native (contract-observation entry '(7) (list (cons (fdefinition pair) :logical-pair))))
                  (effects (copy-list (symbol-value trace))))
              (setf (symbol-value trace) nil)
              (check (eq (car native) :condition))
              (check (equal native (contract-observation (snowgrave:unit-function unit entry) '(7)
                                                         (list (cons (test-code-function unit pair) :logical-pair)))))
              (check (equal effects (symbol-value trace))))))
        (let* ((unknown (append (butlast ordered)
                              (read-from-string "((defun producer (x) (if x (values x 2) (values x))) (defun entry (x) (multiple-value-call #'local-pair (producer x))))")))
               (condition (handler-case (close-it '(mvcall-unproved-value-count) unknown '(t) nil pair)
                            (snowgrave:incomplete-domain (condition) condition))))
          (check (typep condition 'snowgrave:incomplete-domain))
          (check (eq (snowgrave:error-feature condition) :multiple-value-arguments)))))
    (let* ((external '((defun mv-external-producer (x) (values x))
                      (defun mv-external-entry (x) (multiple-value-call #'external-operation (mv-external-producer x)))))
           (unit (snowgrave:close-source-unit
                  (list :forms external) :unit-name '(mvcall-external-effects) :universe '(number)
                  :entries '(mv-external-entry) :external-domains '((mv-external-entry (number)))
                  :external-operations '(external-operation)))
           (*external-log* nil))
      (dolist (form external) (eval form))
      (let ((native (multiple-value-list (mv-external-entry 21))) (effects (copy-list *external-log*)))
        (setf *external-log* nil)
        (check (equal native (multiple-value-list (funcall (snowgrave:unit-function unit 'mv-external-entry) 21))))
        (check (equal effects *external-log*))))
    (let* ((data (read-from-string
                  "((defparameter *mv-first* nil) (defparameter *mv-second* nil)
                     (defun entry (x)
                       (multiple-value-setq (*mv-first* *mv-second*) (values x :tag))
                       (values *mv-first* *mv-second*)))"))
           (unit (snowgrave:close-source-unit
                  (list :forms data) :unit-name '(mvsetq-source-special-data) :universe '(t)
                  :entries (list entry) :external-domains (list (list entry '(t))))))
      (dolist (form data) (eval form))
      (check (equal (multiple-value-list (funcall entry 7))
                    (multiple-value-list (funcall (snowgrave:unit-function unit entry) 7)))))))

(defpackage #:snowgrave.exported.fixture
  (:use #:cl) (:shadow #:identity) (:export #:entry #:metadata-entry #:tag #:identity))

(defun exported-symbol-tests ()
  (let* ((package (find-package "SNOWGRAVE.EXPORTED.FIXTURE"))
         (entry (find-symbol "ENTRY" package))
         (metadata-entry (find-symbol "METADATA-ENTRY" package))
         (tag (find-symbol "TAG" package))
         (identity (find-symbol "IDENTITY" package))
         (unit (snowgrave:close-source-unit
                (list :forms `((defun ,entry () '(,tag ,identity)) (defun ,metadata-entry () 17)))
                :unit-name '(exported-symbol-reader) :entries (list entry metadata-entry)
                :external-domains (list (list entry nil) (list metadata-entry nil))))
         (root (asdf:system-source-directory "snowgrave"))
         (source (merge-pathnames ".build/fresh-exported-symbols.lisp" root))
         (data (merge-pathnames ".build/fresh-exported-symbols.metadata" root)))
    (check (equal (funcall (snowgrave:unit-function unit entry)) (list tag identity)))
    (check (= (funcall (snowgrave:unit-function unit metadata-entry)) 17))
    (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
    (with-open-file (stream data :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
    (check (search "Fresh exported source and metadata symbols executed."
                   (uiop:run-program (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                                           (namestring (merge-pathnames "scripts/fresh-exported-symbols.lisp" root))
                                           (namestring source) (namestring data)) :output :string)))))

(defun namespace-symbol (package name) (intern name package))
(defun namespace-forms ()
  (append
   (let ((*package* (find-package :snowgrave.namespace.a)))
     (read-from-string
      "((defun identity (x) (declare (ignore x)) :wrong-binding)
         (defclass policy () ((payload :initarg :payload :accessor store)))
         (defparameter *state* 10)
         (defgeneric score (p n))
         (defmethod score ((p policy) (n number)) (+ (store p) n *state*))
         (defun private (p) (slot-value p 'payload))
         (defun entry (p n) (+ (score p n) (private p)))
         (defun boot (n) (make-instance 'policy :payload n))
         (defun write-entry (p n) (setf (store p) n) (store p))
         (defun local-identity-entry () (identity 7))
         (defun external-entry (n) (observe n)))"))
   (let ((*package* (find-package :snowgrave.namespace.b)))
     (read-from-string
      "((defclass policy () ((payload :initarg :payload :accessor store)))
         (defparameter *state* 20)
         (defgeneric score (p n))
         (defmethod score ((p policy) (n number)) (+ (store p) n *state*))
         (defun private (p) (slot-value p 'payload))
         (defun entry (p n) (+ (score p n) (private p)))
         (defun boot (n) (make-instance 'policy :payload n))
         (defun write-entry (p n) (setf (store p) n) (store p))
         (defun cl-identity-entry () (cl:identity 7))
         (defun external-entry (n) (observe n)))"))))

(defun namespace-tests ()
  (let* ((a (find-package :snowgrave.namespace.a))
         (b (find-package :snowgrave.namespace.b))
         (forms (namespace-forms))
         (classes (mapcar (lambda (package) (namespace-symbol package "POLICY")) (list a b)))
         (generics (loop for package in (list a b) append
                         (let ((store (namespace-symbol package "STORE")))
                           (list (namespace-symbol package "SCORE") store (list 'setf store)))))
         (entries (append (loop for package in (list a b) append
                                (mapcar (lambda (name) (namespace-symbol package name))
                                        '("ENTRY" "BOOT" "WRITE-ENTRY" "EXTERNAL-ENTRY")))
                          (list (namespace-symbol a "LOCAL-IDENTITY-ENTRY")
                                (namespace-symbol b "CL-IDENTITY-ENTRY"))))
         (domains (append (loop for package in (list a b) for class in classes append
                                (loop for name in '("ENTRY" "BOOT" "WRITE-ENTRY" "EXTERNAL-ENTRY")
                                      for domain in (list (list class 'number) '(number) (list class 'number) '(number))
                                      collect (list (namespace-symbol package name) domain)))
                          (mapcar (lambda (entry) (list entry nil)) (last entries 2))))
         (externals (mapcar (lambda (package) (namespace-symbol package "OBSERVE")) (list a b))))
    (setf (fdefinition (first externals)) (lambda (n) (+ n 100))
          (fdefinition (second externals)) (lambda (n) (+ n 200)))
    ;; The caller's reader environment also shadows CL:IDENTITY. Source and
    ;; metadata replay must not inherit this incidental definition environment.
    (let* ((*package* a)
           (unit (snowgrave:close-source-unit
                  (list :forms forms) :unit-name '(qualified-namespace :version 1)
                  :closed-classes classes :universe (append classes '(number))
                  :closed-generics generics :entries entries :external-domains domains
                  :external-operations externals
                  :external-return-domains (mapcar (lambda (name) (list name '(number))) externals)))
           (metadata (snowgrave:unit-metadata unit))
           (records (loop for package in (list a b) for value in '(3 5)
                          collect (funcall (snowgrave:unit-function unit (namespace-symbol package "BOOT")) value))))
      (check (eq (getf (snowgrave:unit-report unit) :claim) :semantically-closed))
      (check (= (getf metadata :abi-version) 3))
      (check (= (funcall (snowgrave:unit-function unit (namespace-symbol b "CL-IDENTITY-ENTRY"))) 7))
      (check (eq (funcall (snowgrave:unit-function unit (namespace-symbol a "LOCAL-IDENTITY-ENTRY"))) :wrong-binding))
      (signals error (snowgrave:unit-function unit "ENTRY"))
      (signals error (snowgrave:unit-function unit 'cl:identity))
      (check (= (funcall (snowgrave:unit-function unit "CL-IDENTITY-ENTRY")) 7))
      (check (not (eq (snowgrave:sg-record-class (first records)) (snowgrave:sg-record-class (second records)))))
      (check (null (set-exclusive-or
                    (mapcar (lambda (entry) (third (getf entry :definition-key))) (getf metadata :entries))
                    (mapcar #'snowgrave::function-name-key entries) :test #'equal)))
      (check (= (length (remove-duplicates (mapcar (lambda (entry) (getf entry :code-key)) (getf metadata :entries)) :test #'equal))
                (length entries)))
      (dolist (external externals)
        (check (member (snowgrave::function-name-key external) (getf (snowgrave:unit-report unit) :dependencies) :test #'equal)))
      (dolist (form forms) (eval form))
      (loop for package in (list a b) for class in classes for record in records do
        (let* ((entry (namespace-symbol package "ENTRY"))
               (native (make-instance class :payload (snowgrave:sg-record-read record (namespace-symbol package "PAYLOAD")))))
          (check (= (funcall entry native 7) (funcall (snowgrave:unit-function unit entry) record 7)))
          (check (= (funcall (snowgrave:unit-function unit (namespace-symbol package "WRITE-ENTRY")) record 9) 9))
          (check (= (funcall (snowgrave:unit-function unit entry) record 7)
                    (funcall (snowgrave.artifact-tests:artifact-function metadata entry) record 7)))
          (signals snowgrave:domain-violation
            (funcall (snowgrave:unit-function unit entry) (if (eq record (first records)) (second records) (first records)) 7))
          (check (= (funcall (namespace-symbol package "EXTERNAL-ENTRY") 7)
                    (funcall (snowgrave:unit-function unit (namespace-symbol package "EXTERNAL-ENTRY")) 7)))))
      (let* ((root (asdf:system-source-directory "snowgrave"))
             (source (merge-pathnames ".build/fresh-namespace.lisp" root))
             (data (merge-pathnames ".build/fresh-namespace.metadata" root)))
        (with-open-file (stream source :direction :output :if-exists :supersede) (snowgrave:write-unit-source unit stream))
        (with-open-file (stream data :direction :output :if-exists :supersede) (snowgrave:write-unit-metadata unit stream))
        (check (search "Fresh qualified namespaces executed."
                       (uiop:run-program (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                                               (namestring (merge-pathnames "scripts/fresh-namespace.lisp" root))
                                               (namestring source) (namestring data)) :output :string)))))))

(defun ecase-value-tests ()
  ;; Public driver exercise: ordinary MOP method tuples and the actual unmatched
  ;; key condition, with a fresh builder and its own registry/output cache.
  (check (search "ECASE-VALUES-CLOSED:"
                 (uiop:run-program
                  (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                        (namestring (merge-pathnames "scripts/ecase-values-probe.lisp"
                                                     (asdf:system-source-directory "snowgrave"))))
                  :output :string))))

(defun run-tests ()
  (let ((*checks* 0))
    (source-owner-tests)
    (method-source-context-tests)
    (annotation-form-tests)
    (vector-constant-tests)
    (literal-identity-tests)
    (native-literal-graph-tests)
    (predicate-refinement-tests)
    (partition-factorization-tests)
    (external-result-tests)
    (external-value-guard-tests)
    (fixed-generic-call-tests)
    (optional-generic-call-tests)
    (optional-parser-payload-tests)
    (optional-combination-call-tests)
    (generic-required-domain-tests)
    (typed-slot-tests)
    (closed-reference-slot-tests)
    (layout-matching-tests)
    (sequence-fill-tests)
    (sequence-coerce-tests)
    (sequence-shape-tests)
    (native-aggregate-result-tests)
    (immediate-callee-tests)
    (selected-method-root-tests)
    (indirect-result-owner-tests)
    (lambda-opaque-input-tests)
    (local-function-flow-tests)
    (pending-multiple-value-tests)
    (cold-source-boundary-tests)
  (cold-symbol-initializer-tests)
  (deployment-root-tests)
  (cold-method-combination-tests)
  (open-host-operation-tests)
  (cold-integer-initializer-tests)
  (slot-place-normalization-tests)
    (entry-graph-tests)
    (native-binding-context-tests)
    (graph-state-inference-tests)
    (private-container-tests)
    (constructor-state-tests)
    (callable-payload-tests)
    (callable-retention-tests)
    (independent-callable-result-tests)
    (callable-retention-dormant-tests)
    (physical-type-input-tests)
    (generic-error-authority-tests)
    (place-update-input-tests)
    (parser-input-tests)
    (initialization-phase-tests)
    (relational-state-tests)
    (configured-edge-envelope-tests)
    (native-materialization-tests)
    (binding-owner-tests)
    (lambda-scope-tests)
    (lambda-grammar-tests)
    (callable-shadow-tests)
    (callable-flow-tests)
    (callable-reference-escape-tests)
    (callable-union-tests)
    (callable-union-return-tests)
    (returned-callable-local-name-tests)
    (callable-optional-tests)
    (callable-key-tests)
    (destructuring-shadow-tests)
    (multiple-value-closure-tests)
    (multiple-value-binding-tests)
    (generic-method-value-tests)
    (method-call-binding-tests)
    (macro-normalization-tests)
    (authored-combination-tests)
    (check (search "ACTUAL-CHECKPOINT-OWNER-CLOSED:"
                   (uiop:run-program
                    (list "sbcl" "--no-sysinit" "--no-userinit" "--script"
                          (namestring (merge-pathnames "scripts/checkpoint-owner-probe.lisp"
                                                       (asdf:system-source-directory "snowgrave"))))
                    :output :string)))
    (conditional-value-tests)
    (ecase-value-tests)
    (exported-symbol-tests)
    (flow-retention-tests)
    (namespace-tests)
    (mutable-special-tests)
    (record-tests)
    (unit-tests)
    (domain-rejection-tests)
    (record-observation-tests)
    (indirect-record-equality-tests)
    (indirect-operation-tests)
    (mapping-equality-tests)
    (keyword-equality-tests)
    (method-capture-tests)
    (unbound-special-tests)
    (external-operation-tests)
    (external-writer-tests)
    (external-value-representation-tests)
    (sequence-result-domain-tests)
    (precedence-tests)
    (argument-contract-tests)
    (method-initializer-tests)
    (miss-tests)
    (custom-miss-rejection-tests)
    (differential-tests)
    (construction-tests)
    (authored-initialization-tests)
    (initialization-host-rejection-tests)
    (minimum-arity-tests)
    (constructor-error-tests)
    (stable-identity-tests)
    (slot-error-tests)
    (function-flow-tests)
    (return-flow-tests)
    (logical-function-type-tests)
    (slot-protocol-rejection-tests)
    (compiled-root-audit-tests)
    (format t "~&Snowgrave: ~D checks passed.~%" *checks*)
    t))
