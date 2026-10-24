(in-package #:snowgrave)

;; A sealed class table is ordinary emitted data. These queries expose the
;; logical source layout, never the implementation's DEFSTRUCT metaobjects.
(defparameter *metadata-operations*
  '(class-of find-class class-name closer-mop:finalize-inheritance closer-mop:class-slots
    closer-mop:slot-definition-name closer-mop:slot-definition-allocation
    closer-mop:slot-definition-type))

(defun metadata-operation-name (symbol)
  (when (symbolp symbol)
    ;; Match actual MOP symbol identities, never unrelated namesakes.
    (find symbol *metadata-operations* :test #'eq)))

(defun metadata-function-name (build operation phase)
  (let ((canonical (metadata-operation-name operation)))
    (unless canonical
      (unsupported build :metadata-operation "Unsupported metadata operation ~S." operation))
    (if (eq phase :open)
        (if (eq canonical 'find-class)
            (unsupported build :indirect-class-lookup
                         "An indirect FIND-CLASS needs an explicit builder name mapping.")
            canonical)
        (closed-name build
                     (ecase canonical
                       (class-of '%metadata-class-of)
                       (find-class '%metadata-find-class)
                       (class-name '%metadata-class-name)
                       (closer-mop:finalize-inheritance '%metadata-finalize-inheritance)
                       (closer-mop:class-slots '%metadata-class-slots)
                       (closer-mop:slot-definition-name '%metadata-slot-name)
                       (closer-mop:slot-definition-allocation '%metadata-slot-allocation)
                       (closer-mop:slot-definition-type '%metadata-slot-type))))))

(defun metadata-operation-form (build form phase)
  (let ((operation (metadata-operation-name (first form))))
    (when operation
      (values
       (if (eq phase :closed)
           (cons (metadata-function-name build operation phase) (rest form))
           (if (and (eq operation 'find-class) (rest form) (build-classes build))
               (let ((name (gensym "CLASS-NAME")))
                 `(find-class
                   (let ((,name ,(second form)))
                     (or (cdr (assoc ,name ,(record-open-class-registry-name build) :test #'eq))
                         ,name))
                   ,@(cddr form)))
               (cons operation (rest form))))
       t))))

(defun metadata-class-aliases (canonical)
  ;; Resolve host aliases now. Only source symbols are emitted into the table.
  (let ((class (find-class canonical)) (aliases (list canonical)))
    (dolist (package (list-all-packages))
      (let ((symbol (find-symbol (symbol-name canonical) package)))
        (when (and symbol (eq (find-class symbol nil) class))
          (pushnew symbol aliases))))
    aliases))

(defun closed-metadata-object-test (build value)
  (let ((object (gensym "METADATA-OBJECT")))
    `(let ((,object ,value))
       (or (,(closed-name build '%logical-class-p) ,object)
           (,(closed-name build '%logical-slot-p) ,object)))))

(defun closed-class-token-form (build source-class)
  `(,(metadata-function-name build 'find-class :closed) ',source-class))

(defun metadata-class-constructor-name (build)
  (closed-name build '%metadata-class-constructor))

(defun closed-constructor-function-form (build class-form)
  `(,(metadata-class-constructor-name build) ,class-form))

(defun emit-metadata (build)
  (let* ((class-type (closed-name build '%logical-class))
         (class-maker (closed-name build '%make-logical-class))
         (class-p (closed-name build '%logical-class-p))
         (class-name (closed-name build '%logical-class-name))
         (class-slots (closed-name build '%logical-class-slots))
         (class-owned-p (closed-name build '%logical-class-owned-p))
         (class-constructor (closed-name build '%logical-class-constructor))
         (class-printer (closed-name build '%print-logical-class))
         (slot-type (closed-name build '%logical-slot))
         (slot-maker (closed-name build '%make-logical-slot))
         (slot-p (closed-name build '%logical-slot-p))
         (slot-name (closed-name build '%logical-slot-name))
         (slot-allocation (closed-name build '%logical-slot-allocation))
         (slot-value-type (closed-name build '%logical-slot-type))
         (table (closed-name build '%logical-classes))
         (lookup (metadata-function-name build 'find-class :closed))
         (object (gensym "OBJECT"))
         (stream (gensym "STREAM"))
         (depth (gensym "DEPTH"))
         (standard (gensym "STANDARD-CLASS"))
         (effective (gensym "EFFECTIVE-SLOT-CLASS")))
    ;; A custom effective slot definition can change the very facts being
    ;; checked. Refuse it instead of falsely labeling it a stock descriptor.
    (dolist (description (build-layouts build))
      (dolist (slot (closer-mop:class-slots (class-description-open-class description)))
        (unless (eq (class-of slot) (find-class 'closer-mop:standard-effective-slot-definition))
          (unsupported build :slot-metaclass
                       "Slot ~S of ~S requires a stock effective slot definition."
                       (closer-mop:slot-definition-name slot) (class-description-name description)))))
    (emit-form build
               `(defstruct (,class-type (:constructor ,class-maker
                                            (,class-name ,class-slots ,class-owned-p ,class-constructor))
                                        (:predicate ,class-p) (:copier nil) (:conc-name nil)
                                        (:print-function ,class-printer))
                  (,class-name nil :read-only t)
                  (,class-slots nil :read-only t)
                  (,class-owned-p nil :read-only t)
                  (,class-constructor nil :read-only t)))
    (emit-form build
               `(defun ,class-printer (,object ,stream ,depth)
                  (declare (ignore ,depth))
                  (print-unreadable-object (,object ,stream)
                    (write-string "STANDARD-CLASS " ,stream)
                    (prin1 (,class-name ,object) ,stream))))
    (emit-form build
               `(defstruct (,slot-type (:constructor ,slot-maker (,slot-name ,slot-allocation ,slot-value-type))
                                       (:predicate ,slot-p) (:copier nil) (:conc-name nil))
                  (,slot-name nil :read-only t)
                  (,slot-allocation nil :read-only t)
                  (,slot-value-type nil :read-only t)))
    (emit-form build
               `(defparameter ,table
                  (let ((,standard (,class-maker 'standard-class nil nil nil))
                        (,effective (,class-maker 'closer-mop:standard-effective-slot-definition nil nil nil)))
                    (list
                     ,@(loop for alias in (metadata-class-aliases 'standard-class)
                             collect `(cons ',alias ,standard))
                     ,@(loop for alias in (metadata-class-aliases 'closer-mop:standard-effective-slot-definition)
                             collect `(cons ',alias ,effective))
                     ,@(loop for description in (build-layouts build)
                             collect
                             `(cons ',(class-description-name description)
                                    (,class-maker ',(class-description-name description)
                                      (list ,@(loop for slot in (class-description-slots description)
                                                    collect `(,slot-maker ',(slot-description-name slot)
                                                               :instance ',(slot-description-type slot))))
                                      t #',(class-description-constructor description))))))))
    (emit-form build
               `(defun ,(metadata-class-constructor-name build) (,object)
                  (unless (and (,class-p ,object) (,class-owned-p ,object))
                    (error "Only owned classes have closed constructors."))
                  (,class-constructor ,object)))
    (emit-form build
               `(defun ,lookup (name &optional (errorp t) environment)
                  (when environment
                    (error "Lexical class environments are outside the closed metadata table."))
                  (unless (symbolp name) (error 'type-error :datum name :expected-type 'symbol))
                  (or (cdr (assoc name ,table :test #'eq))
                      (when errorp (error "No admitted closed class named ~S." name)))))
    (emit-form build
               `(defun ,(metadata-function-name build 'class-of :closed) (,object)
                  (cond
                    ((,class-p ,object) (,lookup 'standard-class))
                    ((,slot-p ,object) (,lookup 'closer-mop:standard-effective-slot-definition))
                    ,@(loop for description in (build-layouts build)
                            collect `((,(class-description-predicate description) ,object)
                                      (,lookup ',(class-description-name description))))
                    (t (error 'type-error :datum ,object
                              :expected-type '(or ,class-type ,slot-type
                                                  ,@(mapcar #'class-description-type (build-layouts build))))))))
    (emit-form build
               `(defun ,(metadata-function-name build 'class-name :closed) (,object)
                  (,class-name ,object)))
    (dolist (operation '(closer-mop:class-slots closer-mop:finalize-inheritance))
      (emit-form build
                 `(defun ,(metadata-function-name build operation :closed) (,object)
                    (unless (and (,class-p ,object) (,class-owned-p ,object))
                      (error "Only owned classes have closed effective layouts."))
                    ,(if (eq operation 'closer-mop:class-slots)
                         `(,class-slots ,object)
                         nil))))
    (loop for (operation accessor) in
          `((closer-mop:slot-definition-name ,slot-name)
            (closer-mop:slot-definition-allocation ,slot-allocation)
            (closer-mop:slot-definition-type ,slot-value-type))
          do (emit-form build
                        `(defun ,(metadata-function-name build operation :closed) (,object)
                           (,accessor ,object)))))
  build)
