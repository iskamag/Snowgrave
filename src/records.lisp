(in-package #:snowgrave)

;;; The MOP supplies effective slots and precedence. Runtime instances are
;;; ordinary structures; the compiler descriptions below never enter them.

(defstruct slot-description name field type initargs initform initform-p)
(defstruct class-description
  name open-class type allocator constructor predicate bound-accessor slots cpl defaults)

(defun find-record-class (build name)
  (find name (build-layouts build) :key #'class-description-name :test #'eq))

(defun record-helper-name (build name)
  (closed-name build name))

(defun source-class-form (build name)
  (find-if (lambda (form) (and (consp form) (eq (first form) 'defclass)
                              (eq (second form) name)))
           (build-forms build)))

(defun source-class-for-metaobject (build class)
  (find-if (lambda (name) (eq class (find-class (open-name build name) nil)))
           (build-classes build)))

(defun source-slot-initform (build precedence slot-name)
  (dolist (name precedence (values nil nil))
    (let* ((form (source-class-form build name))
           (slot (find slot-name (fourth form)
                       :key (lambda (slot) (if (consp slot) (first slot) slot)))))
      (when (and (consp slot) (member :initform (rest slot)))
        (return (values (getf (rest slot) :initform) t))))))

(defun source-default-initarg (build precedence key)
  (dolist (name precedence)
    (let ((options (rest (assoc :default-initargs (cddddr (source-class-form build name))))))
      (when (loop for tail on options by #'cddr thereis (eq (first tail) key))
        (return-from source-default-initarg (getf options key)))))
  (unsupported build :default-initarg-source "No owned initializer for default initarg ~S." key))

(defun restore-record-type (build type)
  (cond ((symbolp type)
         (or (find-if (lambda (name) (eq type (open-name build name)))
                      (build-classes build)) type))
        ((consp type) (mapcar (lambda (part) (restore-record-type build part)) type))
        (t type)))

(defun record-slot-type-supported-p (build type)
  ;; A SATISFIES predicate or ambient user DEFTYPE would create a second
  ;; untracked call/expansion boundary. Keep the initial storage contract
  ;; to native types and logical class predicates.
  (cond ((symbolp type)
         (or (member type (build-classes build))
             (eq (symbol-package type) (find-package :common-lisp))))
        ((and (consp type) (member (first type) '(and or not)))
         (every (lambda (part) (record-slot-type-supported-p build part)) (rest type)))
        ((and (consp type)
              (member (first type) '(integer rational real float short-float single-float
                                    double-float long-float signed-byte unsigned-byte mod
                                    complex array simple-array vector simple-vector
                                    bit-vector simple-bit-vector string simple-string
                                    base-string simple-base-string cons member eql)))
         (labels ((native-component-p (part)
                    (cond ((member part (build-classes build)) nil)
                          ((consp part) (and (native-component-p (car part))
                                             (native-component-p (cdr part))))
                          ((symbolp part) (or (eq (symbol-package part) (find-package :common-lisp))
                                             (keywordp part)))
                          (t (or (numberp part) (characterp part))))))
           (every #'native-component-p (rest type))))
        (t nil)))

(defun prepare-records (build)
  ;; Stock construction is an explicit initial fragment. Authored protocol
  ;; methods require the same MOP composition path as ordinary generics.
  (dolist (form (build-method-sources build))
    (when (member (second form) '(make-instance allocate-instance initialize-instance
                                 shared-initialize reinitialize-instance
                                 slot-missing slot-unbound))
      (unsupported build :custom-record-protocol
                   "The initial record implementation requires stock ~S behavior." (second form))))
  (setf (build-layouts build)
        (loop for name in (build-classes build)
              for class = (find-class (open-name build name))
              collect
              (progn
                (unless (eq (class-of class) (find-class 'standard-class))
                  (unsupported build :metaclass "Class ~S needs a standard-class layout." name))
                (sb-mop:finalize-inheritance class)
                (let ((precedence
                        (loop for ancestor in (sb-mop:class-precedence-list class)
                              for source = (source-class-for-metaobject build ancestor)
                              when source collect source)))
                  (dolist (parent (sb-mop:class-direct-superclasses class))
                    (unless (or (source-class-for-metaobject build parent)
                                (eq parent (find-class 'standard-object)))
                      (unsupported build :external-superclass
                                   "Superclass ~S of ~S is outside the owned class source."
                                   (class-name parent) name)))
                  (make-class-description
                   :name name :open-class class :type (closed-name build name)
                   :allocator (fresh-name build "ALLOCATE-RECORD")
                   :constructor (fresh-name build "MAKE-RECORD")
                   :predicate (fresh-name build "RECORD-P")
                   :bound-accessor (fresh-name build "RECORD-BOUND")
                   :cpl precedence
                   :defaults (loop for (key) in (sb-mop:class-default-initargs class)
                                   collect (list key (source-default-initarg build precedence key)))
                   :slots
                   (loop for slot in (sb-mop:class-slots class)
                         for slot-name = (sb-mop:slot-definition-name slot)
                         collect
                         (progn
                           (unless (eq (sb-mop:slot-definition-allocation slot) :instance)
                             (unsupported build :class-slot "Class slot ~S in ~S needs shared storage."
                                          slot-name name))
                           (multiple-value-bind (initform presentp)
                               (source-slot-initform build precedence slot-name)
                             (let ((type (restore-record-type build (sb-mop:slot-definition-type slot))))
                              (unless (record-slot-type-supported-p build type)
                                (unsupported build :slot-type "Slot ~S in ~S has unsupported type ~S."
                                             slot-name name type))
                              (make-slot-description
                              :name slot-name :field (fresh-name build "RECORD-FIELD")
                              :type type
                              :initargs (copy-list (sb-mop:slot-definition-initargs slot))
                              :initform initform :initform-p presentp))))))))))
  (dolist (description (build-layouts build))
    (let ((keys (loop for slot in (class-description-slots description)
                      append (slot-description-initargs slot))))
      (dolist (default (class-description-defaults description))
        (unless (or (eq (first default) :allow-other-keys) (member (first default) keys))
          (unsupported build :construction-initargs
                       "Default initarg ~S of ~S has no stock slot initialization."
                       (first default) (class-description-name description))))))
  (build-layouts build))

(defun closed-exact-class-test (build source-class object-form)
  (let ((description (find-record-class build source-class)))
    (unless description
      (unsupported build :record-class "No closed class ~S." source-class))
    `(,(class-description-predicate description) ,object-form)))

(defun closed-class-test (build source-class object-form)
  (let ((object (gensym "RECORD")))
    `(let ((,object ,object-form))
       (or ,@(loop for description in (build-layouts build)
                   when (member source-class (class-description-cpl description))
                     collect `(,(class-description-predicate description) ,object))))))

(defun closed-slot-type-test (build type value)
  (cond ((find-record-class build type) (closed-class-test build type value))
        ((and (consp type) (member (first type) '(and or)))
         (cons (first type) (mapcar (lambda (part) (closed-slot-type-test build part value)) (rest type))))
        ((and (consp type) (eq (first type) 'not) (= (length type) 2))
         `(not ,(closed-slot-type-test build (second type) value)))
        (t `(typep ,value ',type))))

(defun record-reader-form (build object-form slot)
  `(,(record-helper-name build '%record-read) ,object-form ',slot))

(defun record-writer-form (build object-form slot value-form)
  (let ((object (gensym "RECORD")) (value (gensym "VALUE")))
    `(let* ((,object ,object-form) (,value ,value-form))
       (setf (,(record-helper-name build '%record-read) ,object ',slot) ,value))))

(defun emit-record-slot-dispatch (build operation)
  (let* ((reader (record-helper-name build '%record-read))
         (name (case operation
                 (:read reader) (:write `(setf ,reader))
                 (:boundp (record-helper-name build '%record-boundp))
                 (:unbind (record-helper-name build '%record-unbind))))
         (object (gensym "RECORD")) (slot-name (gensym "SLOT")) (value (gensym "VALUE")))
    (emit-form
     build
     `(defun ,name ,(if (eq operation :write) (list value object slot-name) (list object slot-name))
        (cond
          ,@(loop for description in (build-layouts build)
                  collect
                  `((,(class-description-predicate description) ,object)
                    (case ,slot-name
                      ,@(loop for slot in (class-description-slots description) for index from 0
                              for field = (slot-description-field slot)
                              for bound = `(,(class-description-bound-accessor description) ,object)
                              for access = `(,field ,object)
                              collect
                              `((,(slot-description-name slot))
                                ,(case operation
                                   (:read
                                    `(if (logbitp ,index ,bound) ,access
                                         (restart-case
                                             (error 'unbound-slot :instance ,object :name ,slot-name)
                                           (use-value (,value) ,value)
                                           (store-value (,value) (setf (,reader ,object ,slot-name) ,value)))))
                                   (:write
                                    `(progn
                                       (unless ,(closed-slot-type-test build (slot-description-type slot) value)
                                         (error 'type-error :datum ,value :expected-type ',(slot-description-type slot)))
                                       (setf ,access ,value ,bound (logior ,bound ,(ash 1 index)))
                                       ,value))
                                   (:boundp `(logbitp ,index ,bound))
                                   (:unbind `(progn (setf ,access nil ,bound (logandc2 ,bound ,(ash 1 index)))
                                                    ,object)))))
                      (otherwise
                       (error 'sb-pcl::missing-slot :name ,slot-name
                              :format-control "The slot ~S is missing from the object ~S."
                              :format-arguments (list ,slot-name ,object))))))
          (t (error 'type-error :datum ,object
                    :expected-type '(or ,@(mapcar #'class-description-type (build-layouts build))))))))))

(defun emit-record-constructor (build description)
  (let ((args (gensym "INITARGS")) (object (gensym "RECORD"))
        (value (gensym "VALUE")) (presentp (gensym "PRESENT"))
        (lookup (record-helper-name build '%find-initarg)))
    (emit-form
     build
     `(defun ,(class-description-constructor description) (&rest ,args)
        ,@(loop for (key form) in (class-description-defaults description)
                collect
                `(unless (nth-value 1 (,lookup ,args '(,key)))
                   (setf ,args (append ,args (list ',key ,(rewrite-form build form :closed))))))
        (let ((,object (,(class-description-allocator description))))
          ,@(loop for slot in (class-description-slots description)
                  collect
                  `(multiple-value-bind (,value ,presentp)
                       (,lookup ,args ',(slot-description-initargs slot))
                     (cond (,presentp
                            (setf (,(record-helper-name build '%record-read) ,object ',(slot-description-name slot)) ,value))
                           ,@(when (slot-description-initform-p slot)
                               `((t (setf (,(record-helper-name build '%record-read) ,object ',(slot-description-name slot))
                                          ,(rewrite-form build (slot-description-initform slot) :closed))))))))
          ,object)))))

(defun emit-records (build)
  (unless (build-layouts build) (return-from emit-records nil))
  (dolist (description (build-layouts build))
    (emit-form
     build
     `(defstruct (,(class-description-type description)
                   (:constructor ,(class-description-allocator description) ())
                   (:predicate ,(class-description-predicate description))
                   (:copier nil) (:conc-name nil))
        (,(class-description-bound-accessor description) 0 :type integer)
        ,@(mapcar (lambda (slot) `(,(slot-description-field slot) nil))
                  (class-description-slots description)))))
  (emit-form build
             `(defun ,(record-helper-name build '%find-initarg) (arguments keys)
                (loop for (key value) on arguments by #'cddr
                      when (member key keys :test #'eq) return (values value t)
                      finally (return (values nil nil)))))
  (dolist (operation '(:read :write :boundp :unbind))
    (emit-record-slot-dispatch build operation))
  (dolist (description (build-layouts build))
    (emit-record-constructor build description)))

(defun literal-record-symbol (form)
  (when (and (consp form) (eq (first form) 'quote) (null (cddr form)) (symbolp (second form)))
    (values (second form) t)))

(defun record-type-mentioned-p (build type)
  (if (consp type)
      (some (lambda (part) (record-type-mentioned-p build part)) type)
      (member type (build-classes build))))

(defun open-record-type (build type)
  (cond ((member type (build-classes build)) (open-name build type))
        ((consp type) (mapcar (lambda (part) (open-record-type build part)) type))
        (t type)))

(defun record-operation-form (build form phase)
  "Return a replacement and true when this is an owned record operation.
Operands remain source forms for the shared lexical rewriter."
  (let ((operator (first form)))
    (case operator
      (make-instance
       (multiple-value-bind (class literalp) (literal-record-symbol (second form))
         (unless literalp
           (unsupported build :dynamic-construction "MAKE-INSTANCE needs an owned literal class name."))
         (let ((description (find-record-class build class)))
           ;; During the open pass layouts do not yet exist.
           (unless (member class (build-classes build))
             (unsupported build :external-construction "Class ~S has no owned definition." class))
           (if (eq phase :open)
               (values `(make-instance ',(open-name build class) ,@(cddr form)) t)
               (progn
                 (unless (evenp (length (cddr form)))
                   (unsupported build :construction-initargs "MAKE-INSTANCE needs paired literal initarg names."))
                 (let ((allowed (append '(:allow-other-keys)
                                        (loop for slot in (class-description-slots description)
                                              append (slot-description-initargs slot)))))
                   (loop for tail on (cddr form) by #'cddr for key = (first tail)
                         do (unless (and (keywordp key) (member key allowed))
                              (unsupported build :construction-initargs "Unsupported initarg ~S for ~S." key class))))
                 (values `(,(class-description-constructor description) ,@(cddr form)) t))))))
      ((slot-value slot-boundp slot-makunbound)
       (if (eq phase :open) (values form t)
           (multiple-value-bind (slot literalp) (literal-record-symbol (third form))
             (unless literalp
               (unsupported build :dynamic-slot "~S needs a literal slot name." operator))
             (unless (some (lambda (description)
                             (find slot (class-description-slots description) :key #'slot-description-name))
                           (build-layouts build))
               (unsupported build :missing-slot "No owned class defines slot ~S." slot))
             (values `(,(record-helper-name build
                                           (ecase operator (slot-value '%record-read)
                                                   (slot-boundp '%record-boundp) (slot-makunbound '%record-unbind)))
                       ,(second form) ',slot) t))))
      (typep
       (let ((type-form (third form)))
         (when (and (consp type-form) (eq (first type-form) 'quote)
                    (null (cddr type-form)) (record-type-mentioned-p build (second type-form)))
           (let ((type (second type-form)) (value (gensym "TYPE-VALUE")))
             (unless (record-slot-type-supported-p build type)
               (unsupported build :record-type "Unsupported closed class type ~S." type))
             (values (if (eq phase :open)
                         `(typep ,(second form) ',(open-record-type build type))
                         `(let ((,value ,(second form))) ,(closed-slot-type-test build type value))) t))))))))
