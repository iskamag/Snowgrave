(defpackage #:snowgrave.entry-graphs.fixture (:use #:cl))
(in-package #:snowgrave.tests)

(defvar *entry-graph-test-sequence* 0)
(defvar *entry-graph-snapshot-effects* 0)
(defvar *entry-graph-initialization-effects* 0)
(defun entry-graph-test-forms (text)
  (let ((*package* (find-package :snowgrave.entry-graphs.fixture))) (read-from-string text)))
(defun close-entry-graph-test (tag forms entries domains &optional resources external-operations)
  (snowgrave:close-source-unit
   (list :forms forms) :unit-name (list :entry-graphs tag (incf *entry-graph-test-sequence*))
   :closed-classes (loop for form in forms when (eq (car form) 'defclass) collect (second form))
   :universe (append (loop for form in forms when (eq (car form) 'defclass) collect (second form))
                     '(number symbol vector cons t))
   :closed-generics
   (remove-duplicates
    (append (loop for form in forms when (member (car form) '(defgeneric defmethod)) collect (second form))
            (loop for form in forms when (eq (car form) 'defclass) append
              (loop for slot in (fourth form) when (consp slot) append
                (loop for (key value) on (cdr slot) by #'cddr when (eq key :reader) collect value)))) :test #'equal)
   :entries entries :external-domains domains :native-bindings resources
   :external-operations external-operations))
(defun entry-graph-bound-function (unit name)
  (snowgrave:unit-function unit name :bind-configuration t))
(defun entry-graph-refusal (thunk &optional feature)
  (let ((condition (handler-case (progn (funcall thunk) nil) (snowgrave:snowgrave-error (c) c))))
    (check (typep condition 'snowgrave:snowgrave-error))
    (when feature (check (eq feature (snowgrave:error-feature condition))))))

(defun entry-graph-public-tests ()
  (let* ((*package* (find-package :snowgrave.entry-graphs.fixture))
         (forms (entry-graph-test-forms
                 "((defun note-initialization ()
                      (incf snowgrave.tests::*entry-graph-initialization-effects*) nil)
                    (defclass node () ((next :initarg :next :reader next)
                                      (data :initarg :data :reader data)
                                      (spare :initarg :spare) (unbound)
                                      (nil-slot :initform (note-initialization))))
                    (defgeneric clear-node (node))
                    (defmethod clear-node ((node node)) (fill (data node) nil) 0)
                    (defun entry (root twin alias)
                      (values (and (eq root twin) (eq (next root) root)
                                   (eq (data root) alias)
                                   (not (eq (slot-value root 'spare) alias))
                                   (not (slot-boundp root 'unbound))
                                   (slot-boundp root 'nil-slot)
                                   (null (slot-value root 'nil-slot)))
                              (clear-node root) (length (data root))))
                    (defun status () 17))")))
    (dolist (form forms) (eval form))
    (let* ((*entry-graph-initialization-effects* 0)
           (backing (vector 1 2))
           (root (make-instance (intern "NODE") :data backing :spare (vector 1 2))))
      (setf (slot-value root (intern "NEXT")) root)
      (let* ((entry (intern "ENTRY")) (status (intern "STATUS"))
             (unit (close-entry-graph-test
                    :public forms (list entry status)
                    (list (list entry (list (list 'eql root) (list 'eql root) (list 'eql backing)))
                          (list status nil)) (list (list :data backing))))
             (metadata (snowgrave:unit-metadata unit))
             (row (find entry (getf metadata :entries) :key (lambda (row) (getf row :name)))))
        (signals error (snowgrave:unit-function unit entry))
        (check (equal '(t 0 2) (multiple-value-list (funcall (entry-graph-bound-function unit entry)))))
        (check (every #'null backing))
        (check (equal '(t 0 2) (multiple-value-list (funcall (entry-graph-bound-function unit entry)))))
        (check (= 17 (funcall (entry-graph-bound-function unit status))))
        (check (= 1 *entry-graph-initialization-effects*))
        (check (= 3 (length (getf row :lambda-list))))
        (check (null (getf row :bound-lambda-list)))
        (check (getf row :bound-code-key))
        (entry-graph-fresh-test unit)))))

(defun entry-graph-snapshot-tests ()
  (let* ((*package* (find-package :snowgrave.entry-graphs.fixture))
         (base (first (entry-graph-test-forms "((defclass snapshot () ((data :initarg :data))))")))
         (entry (first (entry-graph-test-forms "((defun snapshot-entry (root) (eq root root)))")))
         (class-name (second base)) (entry-name (second entry)))
    (dolist (operation '(sb-mop:class-name sb-mop:class-slots sb-mop:slot-definition-name
                         sb-mop:slot-value-using-class sb-mop:slot-boundp-using-class))
      (eval base)
      (let* ((backing (vector 17)) (root (make-instance class-name :data backing))
             (class (find-class class-name))
             (slot (first (sb-mop:class-slots class)))
             (method
               (eval
                (if (member operation '(sb-mop:slot-value-using-class sb-mop:slot-boundp-using-class))
                    `(defmethod ,operation :around ((class standard-class) (object ,class-name)
                                                   (slot sb-mop:standard-effective-slot-definition))
                       (incf snowgrave.tests::*entry-graph-snapshot-effects*) (call-next-method))
                    `(defmethod ,operation :around ((object (eql ,(if (eq operation 'sb-mop:slot-definition-name) slot class))))
                       (incf snowgrave.tests::*entry-graph-snapshot-effects*) (call-next-method)))))
             (*entry-graph-snapshot-effects* 0))
        (unwind-protect
             (progn
               (entry-graph-refusal
                (lambda () (close-entry-graph-test operation (list base entry) (list entry-name)
                              (list (list entry-name (list (list 'eql root))))
                              (list (list :data backing)))))
               (check (zerop *entry-graph-snapshot-effects*)))
          (remove-method (fdefinition operation) method))))
    (eval base)
    (let* ((old (make-instance class-name :data (vector 17)))
           (method (eval `(defmethod update-instance-for-redefined-class :after
                            ((object ,class-name) added discarded values &rest initargs)
                            (declare (ignore added discarded values initargs))
                            (incf snowgrave.tests::*entry-graph-snapshot-effects*))))
           (*entry-graph-snapshot-effects* 0))
      (unwind-protect
           (progn
             (eval `(defclass ,class-name () ((data :initarg :data) extra)))
             (entry-graph-refusal
              (lambda () (close-entry-graph-test :obsolete (list base entry) (list entry-name)
                            (list (list entry-name (list (list 'eql old)))))) :graph-source-instance)
             (check (zerop *entry-graph-snapshot-effects*)))
        (eval base) (remove-method #'update-instance-for-redefined-class method)))))

(defun entry-graph-fresh-test (unit)
  (let* ((root (asdf:system-source-directory "snowgrave"))
         (cache (merge-pathnames "snowgrave-entry-graph-fresh/" (uiop:temporary-directory))))
    (uiop:with-temporary-file (:pathname source :stream source-stream :type "lisp")
      (snowgrave:write-unit-source unit source-stream)
      (finish-output source-stream)
      (uiop:with-temporary-file (:pathname data :stream data-stream :type "metadata")
        (snowgrave:write-unit-metadata unit data-stream)
        (finish-output data-stream)
        (uiop:with-temporary-file (:pathname driver :stream driver-stream :type "lisp")
          (let ((fasl (compile-file-pathname source)))
            (unwind-protect
                 (progn
                   (dolist (form
                            `((require :asdf)
                              (make-package "SNOWGRAVE.TESTS" :use '("COMMON-LISP"))
                              (asdf:initialize-source-registry
                               '(:source-registry (:directory ,root) :ignore-inherited-configuration))
                              (asdf:initialize-output-translations
                               '(:output-translations (t ,cache) :ignore-inherited-configuration))
                              (asdf:load-system "snowgrave")
                              (assert (not (find-package "SNOWGRAVE.ENTRY-GRAPHS.FIXTURE")))
                              (let* ((identity ',(getf (snowgrave:unit-metadata unit) :identity))
                                     (mode (first (uiop:command-line-arguments)))
                                     (backing (vector 9 8)))
                                (multiple-value-bind (artifact warnings failure) (compile-file ,source :output-file ,fasl)
                                  (declare (ignore warnings)) (assert (not failure))
                                  ;; Package preparation ran during compilation,
                                  ;; but no configuration function is installed.
                                  (let* ((metadata (with-open-file (in ,data) (read in)))
                                         (entry (find "ENTRY" (getf metadata :entries) :test #'string=
                                                      :key (lambda (row) (symbol-name (getf row :name)))))
                                         (key (getf entry :bound-code-key))
                                         (name (find-symbol (second key) (first key))))
                                    (cond
                                      (mode
                                       (let ((condition
                                               (handler-case
                                                   (progn
                                                     (cond ((string= mode "missing") (load artifact))
                                                           ((string= mode "key")
                                                            (snowgrave:with-native-bindings
                                                                (identity (list (list :wrong backing))) (load artifact)))
                                                           ((string= mode "geometry")
                                                            (snowgrave:with-native-bindings
                                                                (identity (list (list :data (vector 1 2 3)))) (load artifact)))
                                                           (t (error "Unknown replay mode"))) nil)
                                                 (snowgrave:snowgrave-error (condition) condition))))
                                         (assert (eq (if (string= mode "geometry") :native-binding-geometry
                                                         :native-binding-missing)
                                                     (snowgrave:error-feature condition)))
                                         (assert (not (fboundp name)))))
                                      (t
                                       (snowgrave:with-native-bindings (identity (list (list :data backing))) (load artifact))
                                       (let ((function (fdefinition name)) (replacement (vector 7 6)))
                                         (assert (equal '(t 0 2) (multiple-value-list (funcall function))))
                                         (assert (every #'null backing))
                                         (let ((condition
                                                 (handler-case
                                                     (snowgrave:with-native-bindings
                                                         (identity (list (list :data replacement))) (load artifact) nil)
                                                   (snowgrave:snowgrave-error (condition) condition))))
                                           (assert (eq :configuration-incarnation (snowgrave:error-feature condition))))
                                         (assert (equalp #(7 6) replacement))
                                         (assert (equal '(t 0 2) (multiple-value-list (funcall function)))))))
                                    (let ((package (find-package "SNOWGRAVE.ENTRY-GRAPHS.FIXTURE")))
                                      (assert (not (find-class (find-symbol "NODE" package) nil)))
                                      (assert (not (fboundp (find-symbol "ENTRY" package))))))))
                              (assert (not (let ((package (find-package "SNOWGRAVE.SBCL")))
                                             (and package (let ((name (find-symbol "CLOSE-SOURCE" package)))
                                                            (and name (fboundp name)))))))
                              (format t "Fresh entry graph checked.~%")))
                     (write form :stream driver-stream :readably t) (terpri driver-stream))
                   (finish-output driver-stream)
                   ;; Each failed install gets a fresh process/namespace: its
                   ;; first-incarnation seal intentionally prevents a retry.
                   (dolist (mode '(nil "missing" "key" "geometry"))
                     (check (search "Fresh entry graph checked."
                                    (uiop:run-program
                                     (append (list "sbcl" "--no-sysinit" "--no-userinit" "--script" (namestring driver))
                                             (when mode (list mode)))
                                     :output :string :error-output *error-output*)))))
              (when (probe-file fasl) (delete-file fasl)))))))))

(defun entry-graph-tests ()
  (entry-graph-declaration-ownership-tests)
  (entry-graph-native-link-tests)
  (entry-graph-public-tests)
  (entry-graph-snapshot-tests)
  (entry-graph-literal-provenance-tests)
  (entry-graph-sparse-import-tests))

(defun entry-graph-declaration-ownership-tests ()
  ;; The same mutable string can be structural metadata and an EQL operand.
  ;; Own only the first role; graph capture must still see the original node.
  (let* ((text (copy-seq "configuration")) (data (vector 17))
         (identity (list :ownership text)) (entry 'snowgrave.entry-graphs.fixture::ownership)
         (adapter (gensym "OWNERSHIP-ADAPTER")) (observed nil))
    (unwind-protect
         (progn
           (snowgrave:register-source-adapter
            adapter (lambda (source declaration)
                      (declare (ignore source)) (setf observed declaration)))
           (snowgrave:close-source-unit
            nil :unit-name identity :entries (list entry) :adapter adapter
            :external-domains (list (list entry (list (list 'eql text) (list 'eql data) (list 'eql data))))
            :native-bindings (list (list :data data)))
           (let ((domains (second (first (getf observed :external-domains)))))
             (check (eq text (second (first domains))))
             (check (eq data (second (second domains))))
             (check (eq data (second (third domains))))
             (check (eq data (second (first (getf observed :native-bindings))))))
           (setf (char text 0) #\X)
           (check (string= "configuration" (second (getf observed :unit-name)))))
      (remhash adapter snowgrave::*source-adapters*))))

(defun entry-graph-native-link-tests ()
  ;; Use the emitted manifest, then substitute fresh resources with equal
  ;; geometry. Repeated edges must stay aliased; opaque scalar contents may vary.
  (let* ((*package* (find-package :snowgrave.entry-graphs.fixture))
         (forms (entry-graph-test-forms
                 "((defclass links () ((data :initarg :data)))
                    (defun links-entry (root) (eq root root)))"))
         (entry (second (second forms))))
    (eval (first forms))
    (labels ((manifest (resource)
               (let* ((root (make-instance (intern "LINKS") :data resource))
                      (unit (close-entry-graph-test
                             :native-links forms (list entry)
                             (list (list entry (list (list 'eql root)))) (list (list :data resource)))))
                 (getf (getf (snowgrave:unit-metadata unit) :configuration) :native-manifest)))
             (resolve (manifest resource)
               (snowgrave:with-native-bindings ('(:link-validation) (list (list :data resource)))
                 (aref (snowgrave::%resolve-native-bindings '(:link-validation) manifest) 0))))
      (let* ((child (vector 17)) (description (manifest (vector child child)))
             (replacement (vector 99)) (shared (vector replacement replacement)))
        (check (eq shared (resolve description shared)))
        (entry-graph-refusal (lambda () (resolve description (vector (vector 17) (vector 17))))
                             :native-binding-alias)
        (setf (aref replacement 0) replacement)
        (entry-graph-refusal (lambda () (resolve description shared)) :native-binding-alias))
      (let ((ring (vector nil)))
        (setf (aref ring 0) ring)
        (let ((description (manifest ring)) (replacement (vector nil)))
          (setf (aref replacement 0) replacement)
          (check (eq replacement (resolve description replacement)))))
      (let* ((child (vector 17)) (dense (make-array 2048 :initial-element child))
             (description (manifest dense)) (replacement (vector 23))
             (shared (make-array 2048 :initial-element replacement)))
        (check (eq shared (resolve description shared)))))))


(defun entry-graph-literal-provenance-tests ()
  (let* ((*package* (find-package :snowgrave.entry-graphs.fixture))
         (class-form
           (first (entry-graph-test-forms
                   "((defclass literal-holder () ((data :initarg :data))))")))
         (class-name (second class-form))
         (entry-name (intern "LITERAL-ENTRY")) (root-name (intern "ROOT"))
         (data-name (intern "DATA")))
    (eval class-form)
    (labels ((close-it (tag root body resource)
               (close-entry-graph-test
                tag (list class-form `(defun ,entry-name (,root-name) ,body))
                (list entry-name) (list (list entry-name (list (list 'eql root))))
                (when resource (list (list :data resource))))))
      ;; The syntax owner copies literals, but a literal originally aliased to
      ;; a captured field must still denote that node, even inside a new outer
      ;; literal. Check both copied configuration data and native imports.
      (dolist (importp '(nil t))
        (dolist (nestedp '(nil t))
          (let* ((data (vector 17))
                 (root (make-instance class-name :data data))
                 (literal (if nestedp (list data) data))
                 (quoted `(quote ,literal))
                 (body `(eq (slot-value ,root-name ',data-name)
                            ,(if nestedp `(car ,quoted) quoted)))
                 (forms (list class-form `(defun ,entry-name (,root-name) ,body))))
            (eval (second forms))
            (check (funcall entry-name root))
            (let ((unit (close-it (list :literal-alias importp nestedp) root body
                                  (when importp data))))
              (check (funcall (entry-graph-bound-function unit entry-name))))
            (check (eq literal (second quoted)))
            (check (if nestedp (eq data (first literal)) (eq data literal)))
            (check (equalp #(17) data)))))
      ;; A deterministic destructive macro edits only normalization's owned
      ;; input. Lineage must not erase that edit by joining it to the original
      ;; graph; failure must leave both the supplied syntax and graph intact.
      (dolist (importp '(nil t))
        (dolist (kind '(:array :cons))
          (let* ((data (if (eq kind :array) (vector 17) (list 17)))
                 (root (make-instance class-name :data data))
                 (quoted `(quote ,data))
                 (edit (if (eq kind :array)
                           '(setf (aref (second datum) 0) 99)
                           '(setf (car (second datum)) 99)))
                 (body `(macrolet ((edited (datum) ,edit datum))
                          (eq (slot-value ,root-name ',data-name) (edited ,quoted))))
                 (resource (when importp (if (arrayp data) data (vector data)))))
            (entry-graph-refusal
             (lambda () (close-it (list :edited-literal importp kind) root body resource))
             :graph-literal-provenance)
            (check (eq data (second quoted)))
            (check (eq data (slot-value root data-name)))
            (check (eql 17 (if (arrayp data) (aref data 0) (car data))))))))))


(defvar *entry-graph-mutated-literal* nil)

(defun entry-graph-sparse-import-tests ()
  (let* ((*package* (find-package :snowgrave.entry-graphs.fixture))
         (forms (entry-graph-test-forms
                 "((defclass sparse-holder () ((data :initarg :data)))
                    (defun sparse-entry (root) (length (slot-value root 'data))))"))
         (class-name (second (first forms))) (entry-name (second (second forms))))
    (eval (first forms))
    (labels ((close-data (data &optional (source forms))
               (let ((root (make-instance class-name :data data)))
                 (close-entry-graph-test
                  :sparse-import source (list entry-name)
                  (list (list entry-name (list (list 'eql root)))) (list (list :data data)))))
             (manifest (unit)
               (getf (getf (snowgrave:unit-metadata unit) :configuration) :native-manifest)))
      ;; A large scalar payload with a few repeated composite edges must keep
      ;; every alias while leaving opaque scalar contents and native storage
      ;; untouched. The manifest describes edges, not one entry per cell.
      (let* ((data (make-array 4096 :initial-element 17)) (child (vector 23)))
        (setf (aref data 3) child (aref data 4095) child)
        (let* ((unit (close-data data)) (nodes (getf (manifest unit) :nodes))
               (outer (find '(4096) nodes :key (lambda (node) (getf node :dimensions)) :test #'equal))
               (links (getf outer :links)))
          (check (= 4096 (funcall (entry-graph-bound-function unit entry-name))))
          (check (= 2 (length nodes)))
          (check (equal '(3 4095) (mapcar #'first links)))
          (check (= (second (first links)) (second (second links))))
          (check (eq child (aref data 3))) (check (eq child (aref data 4095)))
          (check (= 17 (aref data 4094))) (check (= 23 (aref child 0)))))
      ;; A displaced view closes over the entire backing allocation, including
      ;; a cycle through a backing cell outside the view's own visible range.
      (let* ((backing (vector nil 17 23))
             (view (make-array 2 :displaced-to backing :displaced-index-offset 1)))
        (setf (aref backing 0) view)
        (let* ((unit (close-data view)) (nodes (getf (manifest unit) :nodes))
               (view-row (find '(2) nodes :key (lambda (node) (getf node :dimensions)) :test #'equal))
               (backing-row (find '(3) nodes :key (lambda (node) (getf node :dimensions)) :test #'equal)))
          (check (= 2 (funcall (entry-graph-bound-function unit entry-name))))
          (check (= 2 (length nodes)))
          (check (eql (getf backing-row :id) (getf view-row :backing)))
          (check (equal (list (list 0 (getf view-row :id))) (getf backing-row :links)))
          (check (null (getf view-row :links)))
          (check (eq view (aref backing 0)))
          (check (equalp #(17 23) view))))
      ;; Scalar omission is a storage optimization, never permission to skip
      ;; payload admission. Bad leaves at the last physical cell still refuse.
      (dolist (kind '(:hash-table :function :instance))
        (let* ((data (make-array 4096 :initial-element 17))
               (bad (ecase kind
                      (:hash-table (make-hash-table))
                      (:function #'identity)
                      (:instance (make-instance class-name :data nil)))))
          (setf (aref data 4095) bad)
          (entry-graph-refusal
           (lambda () (close-data data))
           (if (eq kind :instance) :graph-native-content :graph-node-kind))
          (check (eq bad (aref data 4095)))
          (check (= 17 (aref data 4094)))))
      ;; Actual numeric/character storage excludes composite payloads without
      ;; reading and boxing every cell. These remain ordinary native imports.
      (dolist (spec (list (list '(unsigned-byte 64) (1- (ash 1 64)))
                          (list 'double-float 1.25d0) (list 'character #\x) (list 'bit 1)))
        (let* ((data (make-array 4096 :element-type (first spec) :initial-element (second spec)))
               (unit (close-data data))
               (nodes (getf (manifest unit) :nodes)))
          (check (= 4096 (funcall (entry-graph-bound-function unit entry-name))))
          (check (= 1 (length nodes)))
          (check (null (getf (first nodes) :links)))
          (check (eql (second spec) (aref data 4095)))))
      ;; Specialized storage does not waive literal snapshot comparison.
      (let* ((data (make-array 1 :element-type '(unsigned-byte 64) :initial-element (1- (ash 1 64))))
             (body `(macrolet ((edited (datum) (setf (aref (second datum) 0) 99) datum))
                      (eq (slot-value root ',(intern "DATA")) (edited ',data))))
             (edited-forms (list (first forms) `(defun ,entry-name (root) ,body))))
        (entry-graph-refusal (lambda () (close-data data edited-forms)) :graph-literal-provenance)
        (check (= (1- (ash 1 64)) (aref data 0))))
      ;; The snapshot cut follows normalization. Matching explicit host and
      ;; copied edits are preserved; copied-only/live-only differences refuse.
      ;; Transitive cons children use the same existing provenance owner.
      (dolist (kind '(:scalar :child))
        (dolist (mode '(:copy-only :live-only :both :discarded-copy))
          (let* ((data (vector (if (eq kind :child) (list 17) 17)))
                 (*entry-graph-mutated-literal* data)
                 (copy-edit (if (eq kind :scalar)
                                '(setf (aref (second datum) 0) 99)
                                '(setf (car (aref (second datum) 0)) 99)))
                 (live-edit (if (eq kind :scalar)
                                '(setf (aref snowgrave.tests::*entry-graph-mutated-literal* 0) 99)
                                '(setf (car (aref snowgrave.tests::*entry-graph-mutated-literal* 0)) 99)))
                 (literal `(macrolet ((edited (datum)
                                       ,@(when (member mode '(:copy-only :both :discarded-copy)) (list copy-edit))
                                       ,@(when (member mode '(:live-only :both)) (list live-edit))
                                       datum))
                             (edited ',data)))
                 (source (if (eq mode :discarded-copy)
                             (append forms (list `(defun ,(intern "DROPPED-LITERAL") () ,literal)))
                             (list (first forms)
                                   `(defun ,entry-name (root)
                                      (eq (slot-value root ',(intern "DATA")) ,literal))))))
            (if (member mode '(:both :discarded-copy))
                (let ((unit (close-data data source)))
                  (check (eql (if (eq mode :both) t 1)
                              (funcall (entry-graph-bound-function unit entry-name)))))
                (entry-graph-refusal (lambda () (close-data data source)) :graph-literal-provenance))
            (check (= (if (member mode '(:live-only :both)) 99 17)
                      (if (eq kind :scalar) (aref data 0) (car (aref data 0)))))))))))
