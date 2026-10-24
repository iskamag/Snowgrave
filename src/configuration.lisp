(in-package #:snowgrave)

;;; A configured entry owns one cold-validated component graph. Only declared
;;; role edges are sealed; ordinary values, arrays and collection state remain
;;; mutable. The compiler selects EMFs and physical slots from its local type
;;; information. An unresolved selector is a compilation error, not a fallback.

(defstruct configuration unit roots roles fields objects names functions selectors calls
  (captures (make-array 0 :adjustable t :fill-pointer 0)))
(defvar *configuration-sequence* 0)
(defvar *configuration* nil)

(defun configured-value (configuration value)
  ;; Borrow a live value without treating it as a quoted immutable literal.
  ;; COMPILE evaluates LOAD-TIME-VALUE now; no compiler environment is retained
  ;; by the result. The object's class is stable, while its data stays mutable.
  (let ((index (vector-push-extend value (configuration-captures configuration)))
        (type (class-name (class-of value))))
    `(the ,type
       (load-time-value (aref (configuration-captures *configuration*) ,index) nil))))

(defun configuration-layout (unit object)
  (when (typep object 'structure-object)
    (find (type-of object) (getf (closed-unit-compiler-data unit) :layouts)
          :key (lambda (layout) (getf layout :type)))))

(defun configuration-slot (layout name)
  (or (find name (getf layout :slots) :key (lambda (slot) (getf slot :name)))
      (unsupported nil :configuration-slot "~S has no slot ~S." (getf layout :name) name)))

(defun prepare-configuration (unit roots declarations)
  (let ((roles (make-hash-table :test #'eq)) (fields (make-hash-table :test #'eq))
        (seen (make-hash-table :test #'eq)))
    (dolist (declaration declarations)
      (let ((layout (find (first declaration) (getf (closed-unit-compiler-data unit) :layouts)
                          :key (lambda (layout) (getf layout :name)))))
        (unless layout
          (unsupported nil :configuration-class "Unknown role class ~S." (first declaration)))
        (dolist (group (rest declaration))
          (dolist (slot (if (symbolp group) (list group) group)) (configuration-slot layout slot)))))
    (labels ((visit (object)
               (let ((layout (configuration-layout unit object)))
                 (when (and layout (not (gethash object seen)))
                   (setf (gethash object seen) layout)
                   (dolist (declaration declarations)
                     (when (member (first declaration) (getf layout :cpl))
                       (dolist (group (rest declaration))
                         (let* ((slots (mapcar (lambda (name) (configuration-slot layout name))
                                              (if (symbolp group) (list group) group)))
                                (values
                                  (mapcar (lambda (slot)
                                            (unless (logbitp (getf slot :index)
                                                             (funcall (getf layout :bound) object))
                                              (unsupported nil :unbound-role "Configuration role ~S is unbound."
                                                           (getf slot :name)))
                                            (let ((value (funcall (getf slot :field) object)))
                                              (unless (or (null value) (configuration-layout unit value))
                                                (unsupported nil :configuration-role
                                                             "Role ~S needs an owned component or NIL, got ~S."
                                                             (getf slot :name) (type-of value)))
                                              value)) slots)))
                           (loop for slot in slots
                                 for existing = (assoc (getf slot :name) (gethash object roles))
                                 do (when existing
                                      (unsupported nil :configuration-role "Repeated role ~S." (getf slot :name)))
                                    (push (cons (getf slot :name) (remove-duplicates values)) (gethash object roles))
                                    (push (cons object (remove-duplicates values)) (gethash (getf slot :field) fields)))
                           (mapc #'visit values)))))))))
      (mapc #'visit roots))
    (make-configuration :unit unit :roots roots :roles roles :fields fields :objects seen
                        :names (make-hash-table :test #'equal)
                        :functions (make-hash-table :test #'equal)
                        :selectors (make-hash-table :test #'equal)
                        :calls (make-hash-table :test #'equal))))

(defun check-configuration-arguments (unit entry arguments)
  (let ((domains (second (assoc entry (getf (closed-unit-compiler-data unit) :entries) :test #'equal))))
    (unless (= (length domains) (length arguments))
      (unsupported nil :configuration-arguments "Entry ~S expects ~D arguments." entry (length domains)))
    (loop for argument in arguments for domain in domains
          unless (typep argument domain)
            do (unsupported nil :configuration-arguments "Argument for ~S does not satisfy ~S." entry domain))))

(defun configured-name (configuration name)
  (or (gethash name (configuration-names configuration)) name))

(defun map-configured-functions (configuration form)
  ;; Unit-private generated function names cannot be authored lexical names.
  ;; Still use the host walker so quoted data, type names, lambda lists and
  ;; lexical function bindings keep their own namespaces.
  (sb-walker:walk-form
   form nil
   (lambda (node context environment)
     (cond ((or (not (eq context :eval)) (atom node)) node)
           ((eq (first node) 'quote) (values node t))
           ((and (eq (first node) 'function) (function-name-p (second node))
                 (not (nth-value 1 (sb-cltl2:function-information (second node) environment))))
            (values (list 'function (configured-name configuration (second node))) t))
           ((and (function-name-p (first node))
                 (not (nth-value 1 (sb-cltl2:function-information (first node) environment)))
                 (gethash (first node) (configuration-names configuration)))
            (cons (configured-name configuration (first node)) (rest node)))
           (t (rewrite-callback-designators
               node (lambda (name ignored) (declare (ignore ignored))
                      (configured-name configuration name))))))))

(defun configured-type-relation (actual expected)
  (cond ((subtypep actual expected) :inside)
        ((subtypep `(and ,actual ,expected) nil) :outside)
        (t :overlap)))

(defun configured-axis-index (axis type)
  (loop for (kind expected) in axis for index from 0
        do (when (member kind '(:any :other)) (return index))
           (case (configured-type-relation type expected)
             (:inside (return index))
             (:overlap (sb-c::give-up-ir1-transform)))))

(defun configured-generic-transform (configuration plan lvars)
  (let* ((required (getf plan :required)) (supplied (- (length lvars) required))
         (parameters (loop repeat (length lvars) collect (gensym "ARGUMENT")))
         (index 0))
    (when (or (getf plan :variable-tail) (not (<= 0 supplied (getf plan :optional))))
      (sb-c::give-up-ir1-transform))
    (loop for axis in (getf plan :axes) for lvar in lvars
          do (setf index (+ (* index (length axis))
                            (configured-axis-index axis (sb-kernel:type-specifier (sb-c::lvar-type lvar))))))
    (let ((clause (find-if (lambda (clause) (member index (first clause))) (getf plan :clauses))))
      (unless clause (sb-c::give-up-ir1-transform))
      `(lambda ,parameters
         (let (,@(loop for variable in (getf plan :arguments) for i from 0
                       collect (list variable (nth i parameters)))
               ,@(when (getf plan :optional-count) (list (list (getf plan :optional-count) supplied)))
               (,(getf plan :overflow) nil))
           ,@(mapcar (lambda (body) (map-configured-functions configuration body)) (rest clause)))))))

(defun configuration-role-guard (rows object &optional value writep)
  `(cond ,@(loop for (owner . allowed) in rows
                 collect `((eq ,object ,(configured-value *configuration* owner))
                           ,(if writep
                                `(unless (member ,value ,(configured-value *configuration* allowed) :test #'eq)
                                   (error "Cannot reconfigure a bound component role."))
                                nil)))
         (t (error "Object is outside the bound component graph."))))

(defun configured-slot-body (configuration plan row)
  (destructuring-bind (type predicate field body) row
    (declare (ignore type predicate))
    (let* ((object (getf plan :object)) (value (getf plan :value))
           (roles (gethash field (configuration-fields configuration)))
           (values (remove-duplicates (loop for row in roles append (copy-list (cdr row)))))
           (types (remove-duplicates (mapcar #'type-of values))))
      (map-configured-functions
       configuration
       (if (null roles) body
           (ecase (getf plan :operation)
             (:read `(progn ,(configuration-role-guard roles object)
                            ,(if (= (length values) 1) (configured-value configuration (first values))
                                 `(the (or ,@types) (,field ,object)))))
             (:boundp `(progn ,(configuration-role-guard roles object) t))
             (:unbind `(error "Cannot unbind a sealed component role."))
             (:write `(progn ,(configuration-role-guard roles object value t) ,body))))))))

(defun configured-slot-transform (configuration plan lvars)
  (let* ((object-index (if (eq (getf plan :operation) :write) 1 0))
         (actual (sb-kernel:type-specifier (sb-c::lvar-type (nth object-index lvars))))
         (row (find-if (lambda (row) (eq (configured-type-relation actual (first row)) :inside))
                       (getf plan :cases))))
    (cond (row `(lambda ,(getf plan :arguments) ,(configured-slot-body configuration plan row)))
          ((= (length (getf plan :cases)) 1)
           ;; A unique physical layout needs a validity check, not selection.
           ;; This also keeps ordinary recursive helpers monomorphic.
           (let ((row (first (getf plan :cases))))
             `(lambda ,(getf plan :arguments)
                (if (,(second row) ,(getf plan :object))
                    ,(configured-slot-body configuration plan row)
                    (,(getf plan :invalid) ,(getf plan :object) ',(getf plan :slot))))))
          (t (sb-c::give-up-ir1-transform)))))

(defun configured-transform (name lvars)
  (unless *configuration* (sb-c::give-up-ir1-transform))
  (let ((plan (gethash name (configuration-selectors *configuration*))))
    (ecase (first plan)
      (:generic (configured-generic-transform *configuration* (second plan) lvars))
      (:slot (configured-slot-transform *configuration* (second plan) lvars)))))

(defun configuration-references (configuration form)
  (let ((names nil))
    (sb-walker:walk-form
     form nil
     (lambda (node context environment)
       (cond ((and (eq context :eval) (consp node) (eq (first node) 'quote)) (values node t))
             (t
              (when (and (eq context :eval) (consp node))
                (let ((name (if (eq (first node) 'function) (second node) (first node))))
                  (when (and (function-name-p name)
                             (gethash name (configuration-functions configuration))
                             (not (nth-value 1 (sb-cltl2:function-information name environment))))
                    (pushnew name names :test #'equal))))
              (when (and (eq context :eval) (consp node))
                (rewrite-callback-designators
                 node (lambda (name ignored)
                        (declare (ignore ignored))
                        (when (gethash name (configuration-functions configuration))
                          (pushnew name names :test #'equal))
                        name)))
              node))))
    names))

(defun configuration-cell-present-p (configuration plan index)
  (loop for axis in (reverse (getf plan :axes))
        for coordinate = (mod index (length axis))
        for cut = (nth coordinate axis)
        always (or (not (eq (first cut) :record))
                   (loop for layout being the hash-values of (configuration-objects configuration)
                         thereis (eq (second cut) (getf layout :type))))
        do (setf index (floor index (length axis)))))

(defun configuration-reachable (configuration entry)
  (let* ((data (closed-unit-compiler-data (configuration-unit configuration)))
         (queue (list entry)) (seen nil))
    (loop while queue for name = (pop queue)
          unless (or (member name seen :test #'equal)
                     (member name (getf data :slow-paths) :test #'equal))
            do (when (member name (getf data :construction-functions) :test #'equal)
                 (unsupported nil :configuration-allocation "Configured entry reaches component construction ~S." name))
               (push name seen)
               (let ((generic (find name (getf data :generics) :key (lambda (plan) (getf plan :name)) :test #'equal))
                     (slot (find name (getf data :slots) :key (lambda (plan) (getf plan :name)) :test #'equal)))
                 (cond
                   (generic
                    (dolist (clause (getf generic :clauses))
                      (when (some (lambda (index) (configuration-cell-present-p configuration generic index)) (first clause))
                        (dolist (body (rest clause))
                          (setf queue (append (configuration-references configuration body) queue))))))
                   (slot nil)
                   (t
                    (let ((definition (gethash name (configuration-functions configuration))))
                      (setf queue (append (configuration-references configuration
                                                                  (cons 'lambda (cddr definition))) queue)))))))
    (nreverse seen)))

(defun configuration-callable-name (lvar)
  (or (and lvar (sb-c::lvar-fun-name lvar t))
      (when (and lvar (sb-c::constant-lvar-p lvar))
        (let ((value (sb-c::lvar-value lvar)))
          (if (null value) 'identity (and (symbolp value) value))))
      :indirect))

(defun configuration-callback-references (name node)
  (when (sb-c::combination-p node)
    (let* ((arguments (sb-c::combination-args node))
           (calls (loop for position in (rest (assoc name *callback-arguments*))
                        collect (configuration-callable-name (nth position arguments))))
           (start (cdr (assoc name *callback-keywords*))))
      (when start
        (loop for (key value) on (nthcdr start arguments) by #'cddr
              do (cond ((or (null key) (not (sb-c::constant-lvar-p key)))
                        ;; A computed option may become :KEY or :TEST later.
                        (pushnew :indirect calls))
                       ((member (sb-c::lvar-value key) '(:key :test :test-not))
                        (pushnew (configuration-callable-name value) calls :test #'equal)))))
      calls)))

(defun configuration-function-reference (node)
  (when (sb-c::ref-p node)
    (let ((leaf (sb-c::ref-leaf node)))
      (cond ((and (sb-c::global-var-p leaf) (eq (sb-c::global-var-kind leaf) :global-function))
             (sb-c::leaf-source-name leaf))
            ((and (sb-c::constant-p leaf) (symbolp (sb-c::constant-value leaf))
                  (or (gethash (sb-c::constant-value leaf) (configuration-functions *configuration*))
                      (gethash (sb-c::constant-value leaf) (configuration-selectors *configuration*))))
             (sb-c::constant-value leaf))))))

(defun configuration-compiled-calls (component)
  ;; Inspect final optimized IR, including indirect calls and escaping function
  ;; values. A static callee-list API omits these dependencies.
  (let ((calls nil))
    (loop for block = (sb-c::block-next (sb-c::component-head component)) then (sb-c::block-next block)
          until (eq block (sb-c::component-tail component))
          do (loop for node = (sb-c::ctran-next (sb-c::block-start block))
                     then (let ((next (sb-c::node-next node))) (and next (sb-c::ctran-next next)))
                   while node
                   do (let ((name (configuration-function-reference node)))
                        (when name (pushnew name calls :test #'equal)))
                   when (and (sb-c::basic-combination-p node)
                             (not (eq (sb-c::basic-combination-kind node) :local)))
                     do (let ((name (sb-c::lvar-fun-name (sb-c::basic-combination-fun node) t)))
                          (pushnew (or name :indirect) calls :test #'equal)
                          (setf calls (union calls (configuration-callback-references name node) :test #'equal)))))
    calls))

(defun compile-configuration-function (configuration name lambda-form &key inline)
  (let ((calls nil))
    (let ((sb-c::*compile-component-hook*
            (lambda (component)
              (setf calls (union calls (configuration-compiled-calls component) :test #'equal)))))
      (let ((function (if inline
                          (progn (eval `(defun ,name ,@(rest lambda-form))) (fdefinition name))
                          (multiple-value-bind (function warnings failure) (compile name lambda-form)
                            (declare (ignore warnings))
                            (when failure (unsupported nil :configuration-compilation "Cannot compile ~S." name))
                            function))))
        (setf (gethash name (configuration-calls configuration)) calls)
        function))))

(defun audit-configuration-calls (configuration entry)
  (let ((queue (list entry)) (seen nil) (data (closed-unit-compiler-data (configuration-unit configuration))))
    (loop while queue for name = (pop queue)
          unless (member name seen :test #'equal)
            do (push name seen)
               (dolist (callee (gethash name (configuration-calls configuration)))
                 (cond ((eq callee :indirect)
                        (unsupported nil :configuration-indirect-call "Unresolved function value in ~S." name))
                       ((gethash callee (configuration-selectors configuration))
                        (unsupported nil :configuration-dispatch "Unresolved configured selector ~S in ~S." callee name))
                       ((gethash callee (configuration-calls configuration)) (push callee queue))
                       ((and (gethash callee (configuration-functions configuration))
                             (not (member callee (getf data :slow-paths) :test #'equal)))
                        (unsupported nil :configuration-open-call "Unspecialized owned function ~S in ~S." callee name))
                       ((find callee (getf data :layouts) :key (lambda (layout) (getf layout :allocator)))
                        (unsupported nil :configuration-allocation "Configured entry constructs an owned component.")))))
    t))

(defun check-configuration-seals (configuration)
  (let ((previous (closed-unit-seals (configuration-unit configuration))))
    (maphash
     (lambda (object slots)
       (dolist (slot slots)
         (let ((old (assoc (car slot) (gethash object previous))))
           (when (and old (or (set-difference (cdr slot) (cdr old)) (set-difference (cdr old) (cdr slot))))
             (unsupported nil :configuration-seal "Binding would change an existing role seal for ~S." (car slot))))))
     (configuration-roles configuration))))

(defun publish-configuration-seals (configuration)
  (let* ((unit (configuration-unit configuration)) (registry (make-hash-table :test #'eq)) (wrappers nil))
    (maphash (lambda (object slots) (setf (gethash object registry) (copy-list slots))) (closed-unit-seals unit))
    (maphash (lambda (object slots)
               (dolist (slot slots) (pushnew slot (gethash object registry) :key #'car)))
             (configuration-roles configuration))
    (dolist (plan (getf (closed-unit-compiler-data unit) :slots))
      (when (member (getf plan :operation) '(:write :unbind))
        (let* ((name (getf plan :name))
               (rows (loop for object being the hash-keys of registry using (hash-value slots)
                           for slot = (assoc (getf plan :slot) slots)
                           when slot collect (cons object (cdr slot)))))
          (when rows
            (let ((original (or (gethash name (closed-unit-sealed-writers unit)) (fdefinition name)))
                  (object (getf plan :object)) (value (getf plan :value)))
              (multiple-value-bind (function warnings failure)
                  (compile nil
                             `(lambda ,(getf plan :arguments)
                                (cond ,@(loop for (owner . allowed) in rows
                                              collect `((eq ,object ,(configured-value configuration owner))
                                                        ,(if (eq (getf plan :operation) :unbind)
                                                             `(error "Cannot unbind a sealed component role.")
                                                             `(unless (member ,value ,(configured-value configuration allowed) :test #'eq)
                                                                (error "Cannot reconfigure a bound component role."))))))
                                (funcall ,(configured-value configuration original) ,@(getf plan :arguments))))
                (declare (ignore warnings))
                (when failure
                  (unsupported nil :configuration-seal "Cannot compile role guard ~S." name))
                (push (list name original function) wrappers)))))))
    ;; Complete compilation before publishing any changed function or seal.
    (dolist (wrapper wrappers)
      (setf (gethash (first wrapper) (closed-unit-sealed-writers unit)) (second wrapper)
            (fdefinition (first wrapper)) (third wrapper)))
    (setf (closed-unit-seals unit) registry)))

(defun bind-entry (unit entry arguments &key roles)
  "Compile a zero-argument entry bound to ARGUMENTS and seal declared ROLES.
ROLES contains (SOURCE-CLASS SLOT...) declarations. A list in place of SLOT
declares an exchange group, e.g. (CHENEY (SOURCE DESTINATION)). Its slots may
exchange their validated component identities; other component replacements
and unbinding are rejected. Native data slots are not configuration roles.
This SBCL hosted binding returns a live function, not a serialized image."
  (unit-function unit entry)
  (check-configuration-arguments unit entry arguments)
  (let* ((configuration (prepare-configuration unit arguments roles))
         (*configuration* configuration)
         (metadata (find entry (getf (closed-unit-metadata unit) :entries) :key (lambda (row) (getf row :name))))
         (key (getf metadata :code-key))
         (original (find-symbol (second key) (first key)))
         (package (make-package (format nil "SNOWGRAVE.CONFIGURATION.~D" (incf *configuration-sequence*)) :use '("COMMON-LISP")))
         (target (intern "%BOUND-ENTRY" package))
         (success nil))
    (unwind-protect
         (progn
           (check-configuration-seals configuration)
           (dolist (form (closed-unit-source unit))
             (when (eq (first form) 'defun)
               (setf (gethash (second form) (configuration-functions configuration)) form)))
           (let* ((names (configuration-reachable configuration original))
                  (data (closed-unit-compiler-data unit)))
             (dolist (name names)
               (let ((text (symbol-name (if (consp name) (second name) name))))
                 (shadow text package)
                 (setf (gethash name (configuration-names configuration))
                       (if (consp name) (list 'setf (intern text package)) (intern text package)))))
             (dolist (kind '(:generic :slot))
               (dolist (plan (getf data (if (eq kind :generic) :generics :slots)))
                 (let ((name (gethash (getf plan :name) (configuration-names configuration))))
                   (when name
                     (setf (gethash name (configuration-selectors configuration)) (list kind plan))
                     (eval `(defun ,name (&rest arguments) (declare (ignore arguments))
                              (error "Unresolved configured call.")))
                     (eval `(sb-c:defknown ,name (&rest t) * (sb-c::any) :overwrite-fndb-silently t))
                     (eval `(sb-c:deftransform ,name ((&rest arguments) * * :important nil)
                              (configured-transform ',name arguments)))))))
             (let ((ordinary (remove-if (lambda (name)
                                         (gethash (configured-name configuration name) (configuration-selectors configuration)))
                                       names)))
               (proclaim `(inline ,@(mapcar (lambda (name) (configured-name configuration name)) ordinary)))
               ;; Install original definitions in source order. Saved inline
               ;; expansions expose later helper bindings at the bound call.
               (dolist (form (closed-unit-source unit))
                 (when (and (eq (first form) 'defun) (member (second form) ordinary :test #'equal))
                   (compile-configuration-function
                    configuration (configured-name configuration (second form))
                    (map-configured-functions configuration (cons 'lambda (cddr form))) :inline t))))
             (let* ((lambda-form `(lambda () (,(configured-name configuration original)
                                             ,@(mapcar (lambda (value) (configured-value configuration value)) arguments))))
                    (function (compile-configuration-function configuration target lambda-form)))
               (audit-configuration-calls configuration target)
               (publish-configuration-seals configuration)
               (setf success t)
               function)))
      (unless success
        (do-symbols (symbol package)
          (when (eq (symbol-package symbol) package)
            (when (fboundp symbol) (fmakunbound symbol))
            (when (fboundp (list 'setf symbol)) (fmakunbound (list 'setf symbol)))))
        (delete-package package)))))
