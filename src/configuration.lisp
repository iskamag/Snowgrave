(in-package #:snowgrave)

;;; A configured entry owns one cold-validated component graph. Only declared
;;; role edges are sealed; ordinary values, arrays and collection state remain
;;; mutable. Source specialization selects EMFs and physical slots from declared
;;; roles and lexical facts. An unresolved selector is rejected before compilation.

(defstruct configuration unit roots roles fields objects names functions specializations emitted
  (captures (make-array 0 :adjustable t :fill-pointer 0))
  (identities (make-hash-table :test #'eq)))
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
                        :specializations (make-hash-table :test #'equal))))

(defun check-configuration-arguments (unit entry arguments)
  (let ((domains (second (assoc entry (getf (closed-unit-compiler-data unit) :entries) :test #'equal))))
    (unless (= (length domains) (length arguments))
      (unsupported nil :configuration-arguments "Entry ~S expects ~D arguments." entry (length domains)))
    (loop for argument in arguments for domain in domains
          unless (typep argument domain)
            do (unsupported nil :configuration-arguments "Argument for ~S does not satisfy ~S." entry domain))))

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
      (if (null roles) body
           (ecase (getf plan :operation)
             (:read `(progn ,(configuration-role-guard roles object)
                            ,(if (= (length values) 1) (configured-value configuration (first values))
                                 `(the (or ,@types) (,field ,object)))))
             (:boundp `(progn ,(configuration-role-guard roles object) t))
             (:unbind `(error "Cannot unbind a sealed component role."))
             (:write `(progn ,(configuration-role-guard roles object value t) ,body)))))))

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
