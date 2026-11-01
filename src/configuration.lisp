(in-package #:snowgrave)

;;; A configured entry owns one cold-validated component graph. Only declared
;;; role edges are sealed; ordinary values, arrays and collection state remain
;;; mutable. Source specialization selects EMFs and physical slots from declared
;;; roles and lexical facts. An unresolved selector is rejected before compilation.

(defstruct configuration
  unit roles fields entry write-fields emitted
  (functions (make-hash-table :test #'equal))
  (specializations (make-hash-table :test #'equal))
  (mutations (make-hash-table :test #'eq))
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
    (find (type-of object) (unit-plan-layouts (closed-unit-plan unit))
          :key #'class-description-type)))

(defun configuration-slot (layout name)
  (or (find name (class-description-slots layout) :key #'slot-description-name)
      (unsupported :configuration-slot "~S has no slot ~S." (class-description-name layout) name)))

(defun validate-role-declarations (unit declarations)
  (dolist (declaration declarations)
    (let ((layout (find (first declaration) (unit-plan-layouts (closed-unit-plan unit))
                        :key #'class-description-name)))
      (unless layout
        (unsupported :configuration-class "Unknown role class ~S." (first declaration)))
      (dolist (group (rest declaration))
        (dolist (slot (if (symbolp group) (list group) group))
          (configuration-slot layout slot))))))

(defun configuration-role-values (unit layout object slots)
  (mapcar (lambda (slot)
            (unless (logbitp (slot-description-index slot) (funcall (class-description-bound-accessor layout) object))
              (unsupported :unbound-role "Configuration role ~S is unbound." (slot-description-name slot)))
            (let ((value (funcall (slot-description-field slot) object)))
              (unless (or (null value) (configuration-layout unit value))
                (unsupported :configuration-role
                             "Role ~S needs an owned component or NIL, got ~S."
                             (slot-description-name slot) (type-of value)))
              value))
          slots))

(defun register-role-group (configuration layout object group)
  (let* ((names (if (symbolp group) (list group) group))
         (slots (mapcar (lambda (name) (configuration-slot layout name)) names))
         (values (configuration-role-values (configuration-unit configuration) layout object slots))
         (allowed (remove-duplicates values))
         (roles (configuration-roles configuration))
         (fields (configuration-fields configuration)))
    (dolist (slot slots)
      (when (assoc (slot-description-name slot) (gethash object roles))
        (unsupported :configuration-role "Repeated role ~S." (slot-description-name slot)))
      (push (cons (slot-description-name slot) allowed) (gethash object roles))
      (push (cons object allowed) (gethash (slot-description-field slot) fields)))
    values))

(defun prepare-configuration (unit roots declarations)
  (validate-role-declarations unit declarations)
  (let ((configuration (make-configuration
                        :unit unit
                        :roles (make-hash-table :test #'eq)
                        :fields (make-hash-table :test #'eq)))
        (seen (make-hash-table :test #'eq)))
    (labels ((visit (object)
               (let ((layout (configuration-layout unit object)))
                 (when (and layout (not (gethash object seen)))
                   (setf (gethash object seen) t)
                   (dolist (declaration declarations)
                     (when (member (first declaration) (class-description-cpl layout))
                       (dolist (group (rest declaration))
                         (mapc #'visit (register-role-group configuration layout object group)))))))))
      (mapc #'visit roots))
    configuration))

(defun check-configuration-arguments (unit entry arguments)
  (let ((domains (second (assoc entry (unit-plan-entries (closed-unit-plan unit)) :test #'equal))))
    (unless (= (length domains) (length arguments))
      (unsupported :configuration-arguments "Entry ~S expects ~D arguments." entry (length domains)))
    (loop for argument in arguments for domain in domains
          unless (typep argument domain)
            do (unsupported :configuration-arguments "Argument for ~S does not satisfy ~S." entry domain))))

(defun configuration-role-guard (configuration rows object
                                 &key (operation :read) value (require-owner t))
  `(cond ,@(loop for (owner . allowed) in rows
                 collect `((eq ,object ,(configured-value configuration owner))
                           ,(case operation
                              (:write
                               `(unless (member ,value ,(configured-value configuration allowed) :test #'eq)
                                  (error "Cannot reconfigure a bound component role.")))
                              (:unbind `(error "Cannot unbind a sealed component role.")))))
         ,@(when require-owner '((t (error "Object is outside the bound component graph."))))))

(defun index-configuration-write-seals (unit registry)
  "Index a cold seal snapshot by physical field, without changing read facts."
  (let ((fields (make-hash-table :test #'eq)))
    (maphash
     (lambda (owner slots)
       (let ((layout (configuration-layout unit owner)))
         (dolist (slot slots)
           (push (cons owner (cdr slot))
                 (gethash (slot-description-field (configuration-slot layout (car slot))) fields)))))
     registry)
    fields))

(defun configured-slot-body (configuration plan row)
  (let* ((field (slot-case-field row)) (body (slot-case-body row))
         (object (slot-plan-object plan)) (value (slot-plan-value plan))
         (roles (gethash field (configuration-fields configuration)))
         (values (remove-duplicates (loop for row in roles append (copy-list (cdr row)))))
         (types (remove-duplicates (mapcar #'type-of values))))
    (if (null roles)
        (let ((seals (gethash field (configuration-write-fields configuration))))
          (if (and seals (member (slot-plan-operation plan) '(:write :unbind)))
              `(progn ,(configuration-role-guard configuration seals object
                         :operation (slot-plan-operation plan) :value value :require-owner nil)
                      ,body)
              body))
        (ecase (slot-plan-operation plan)
          (:read `(progn ,(configuration-role-guard configuration roles object)
                         ,(if (= (length values) 1) (configured-value configuration (first values))
                              `(the (or ,@types) (,field ,object)))))
          (:boundp `(progn ,(configuration-role-guard configuration roles object) t))
          (:unbind `(error "Cannot unbind a sealed component role."))
          (:write `(progn ,(configuration-role-guard configuration roles object
                            :operation :write :value value) ,body))))))

(defun check-configuration-seals (configuration)
  (let ((previous (closed-unit-seals (configuration-unit configuration))))
    (maphash
     (lambda (object slots)
       (dolist (slot slots)
         (let ((old (assoc (car slot) (gethash object previous))))
           (when (and old (or (set-difference (cdr slot) (cdr old)) (set-difference (cdr old) (cdr slot))))
             (unsupported :configuration-seal "Binding would change an existing role seal for ~S." (car slot))))))
     (configuration-roles configuration))))

(defun merged-configuration-seals (configuration)
  (let ((registry (make-hash-table :test #'eq)) (changed (make-hash-table :test #'eq))
        (unit (configuration-unit configuration)))
    (maphash (lambda (object slots) (setf (gethash object registry) (copy-list slots)))
             (closed-unit-seals (configuration-unit configuration)))
    (maphash (lambda (object slots)
               (dolist (slot slots)
                 (unless (assoc (car slot) (gethash object registry))
                   (push slot (gethash object registry))
                   (setf (gethash (slot-description-field
                                  (configuration-slot (configuration-layout unit object) (car slot)))
                                 changed) t))))
             (configuration-roles configuration))
    (values registry changed)))

(defun compile-sealed-writer (configuration plan registry)
  (let* ((unit (configuration-unit configuration))
         (name (slot-plan-name plan))
         (object (slot-plan-object plan))
         (value (slot-plan-value plan))
         (rows (loop for owner being the hash-keys of registry using (hash-value slots)
                     for slot = (assoc (slot-plan-slot plan) slots)
                     when slot collect (cons owner (cdr slot)))))
    (when rows
      (let* ((original (or (gethash name (closed-unit-sealed-writers unit)) (fdefinition name)))
             (source
               `(lambda ,(slot-plan-arguments plan)
                  ,(configuration-role-guard configuration rows object
                     :operation (slot-plan-operation plan) :value value :require-owner nil)
                  (funcall ,(configured-value configuration original) ,@(slot-plan-arguments plan)))))
        (list name original (compile-function nil source :configuration-seal))))))
