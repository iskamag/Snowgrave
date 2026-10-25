(in-package #:snowgrave)

;;; The MOP supplies effective slots and precedence. Runtime instances are
;;; ordinary structures; the compiler descriptions below never enter them.

(defstruct slot-description name field type initargs initform initform-p)
(defstruct class-description
  name type allocator constructor predicate bound-accessor slots cpl defaults)

(defun find-record-class (build name)
  (find name (build-layouts build) :key #'class-description-name :test #'eq))

(defun record-make-instance-name (build phase)
  (if (eq phase :closed)
      (let ((package (build-output-package build)))
        (shadow "MAKE-INSTANCE" package)
        (intern "MAKE-INSTANCE" package))
      (open-name build '%make-instance)))

(defun emit-open-record-helpers (build)
  "Keep stage-one construction in its isolated CLOS class namespace."
  (when (build-classes build)
    (let ((class (gensym "CLASS")) (initargs (gensym "INITARGS"))
          (binding (gensym "BINDING")) (target (gensym "TARGET"))
          (registry (open-name build '%source-class-names)))
      (compile-definition `(defparameter ,registry
          ',(loop for source-class in (build-classes build)
                  collect (cons source-class (open-name build source-class)))))
      (compile-definition `(defun ,(record-make-instance-name build :open) (,class &rest ,initargs)
          (let ((,target
                  (if (symbolp ,class)
                      (let ((,binding (assoc ,class ,registry :test #'eq)))
                        (cond (,binding (find-class (cdr ,binding)))
                              ((member ,class ,registry :key #'cdr :test #'eq)
                               (find-class ,class))
                              (t (error 'simple-error :format-control "No owned class named ~S."
                                        :format-arguments (list ,class)))))
                      ,class)))
            (apply #'make-instance ,target ,initargs)))))))

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
      (when (and (consp slot)
                 (loop for (key) on (rest slot) by #'cddr thereis (eq key :initform)))
        (return (values (getf (rest slot) :initform) t))))))

(defun source-default-initarg (build precedence key)
  (dolist (name precedence)
    (let ((options (rest (assoc :default-initargs (cddddr (source-class-form build name))))))
      (when (loop for tail on options by #'cddr thereis (eq (first tail) key))
        (return-from source-default-initarg (getf options key)))))
  (unsupported :default-initarg-source "No owned initializer for default initarg ~S." key))

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
  (when (representation-sensitive-type-p type)
    (return-from record-slot-type-supported-p nil))
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

(defun validate-record-protocol (build)
  ;; Stock construction is an explicit initial fragment. Authored protocol
  ;; methods require the same MOP composition path as ordinary generics.
  (dolist (form (build-method-sources build))
    (when (member (second form) '(make-instance allocate-instance initialize-instance
                                 shared-initialize reinitialize-instance
                                 slot-missing slot-unbound))
      (unsupported :custom-record-protocol
                   "The initial record implementation requires stock ~S behavior." (second form)))))

(defun prepare-slot-description (build class-name precedence slot)
  (let ((name (closer-mop:slot-definition-name slot))
        (type (restore-record-type build (closer-mop:slot-definition-type slot))))
    (unless (eq (class-of slot) (find-class 'closer-mop:standard-effective-slot-definition))
      (unsupported :slot-metaclass "Slot ~S of ~S requires a stock effective slot definition."
                   name class-name))
    (unless (eq (closer-mop:slot-definition-allocation slot) :instance)
      (unsupported :class-slot "Class slot ~S in ~S needs shared storage." name class-name))
    (unless (record-slot-type-supported-p build type)
      (unsupported :slot-type "Slot ~S in ~S has unsupported type ~S." name class-name type))
    (multiple-value-bind (initform presentp) (source-slot-initform build precedence name)
      (make-slot-description
       :name name :field (fresh-name build "RECORD-FIELD") :type type
       :initargs (copy-list (closer-mop:slot-definition-initargs slot))
       :initform initform :initform-p presentp))))

(defun prepare-class-description (build name)
  (let ((class (find-class (open-name build name))))
    (unless (eq (class-of class) (find-class 'standard-class))
      (unsupported :metaclass "Class ~S needs a standard-class layout." name))
    (closer-mop:finalize-inheritance class)
    (dolist (parent (closer-mop:class-direct-superclasses class))
      (unless (or (source-class-for-metaobject build parent)
                  (eq parent (find-class 'standard-object)))
        (unsupported :external-superclass
                     "Superclass ~S of ~S is outside the owned class source."
                     (class-name parent) name)))
    (let ((precedence (loop for ancestor in (closer-mop:class-precedence-list class)
                            for source = (source-class-for-metaobject build ancestor)
                            when source collect source)))
      (make-class-description
       :name name :type (closed-name build name)
       :allocator (fresh-name build "ALLOCATE-RECORD")
       :constructor (fresh-name build "MAKE-RECORD")
       :predicate (fresh-name build "RECORD-P")
       :bound-accessor (fresh-name build "RECORD-BOUND")
       :cpl precedence
       :defaults (loop for (key) in (closer-mop:class-default-initargs class)
                       collect (list key (source-default-initarg build precedence key)))
       :slots (mapcar (lambda (slot) (prepare-slot-description build name precedence slot))
                      (closer-mop:class-slots class))))))

(defun prepare-records (build)
  (setf (build-layouts build)
        (mapcar (lambda (name) (prepare-class-description build name)) (build-classes build))))

(defun closed-exact-class-test (build source-class object-form)
  (let ((description (find-record-class build source-class)))
    (unless description
      (unsupported :record-class "No closed class ~S." source-class))
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

(defun record-operation-helper (build operation)
  (let ((reader (closed-name build '%record-read)))
    (ecase operation
      (:read reader) (:write `(setf ,reader))
      (:boundp (closed-name build '%record-boundp))
      (:unbind (closed-name build '%record-unbind)))))

(defun record-slot-function (build operation slot)
  (if (eq operation :write)
      `(setf ,(record-slot-function build :read slot))
      (let ((key (list operation slot)))
        (or (gethash key (build-slot-functions build))
            (setf (gethash key (build-slot-functions build))
                  (fresh-name build (format nil "SLOT-~A" operation)))))))

(defun known-record-slot-p (build slot)
  (some (lambda (description)
          (find slot (class-description-slots description) :key #'slot-description-name))
        (build-layouts build)))

(defun record-reader-form (build object-form slot)
  `(,(record-slot-function build :read slot) ,object-form))

(defun record-writer-form (build object-form slot value-form)
  (let ((object (gensym "RECORD")) (value (gensym "VALUE")))
    `(let* ((,object ,object-form) (,value ,value-form))
       (setf (,(record-slot-function build :read slot) ,object) ,value))))

(defun record-slot-body (build description slot operation object value)
  (let* ((index (position slot (class-description-slots description)))
         (bound `(,(class-description-bound-accessor description) ,object))
         (access `(,(slot-description-field slot) ,object)))
    (ecase operation
      (:read `(if (logbitp ,index ,bound) ,access
                  (,(closed-name build '%record-unbound)
                   ,object ',(slot-description-name slot))))
      (:write
       `(progn
          (unless ,(closed-slot-type-test build (slot-description-type slot) value)
            (error 'type-error :datum ,value :expected-type ',(slot-description-type slot)))
          (setf ,access ,value ,bound (logior ,bound ,(ash 1 index)))
          ,value))
      (:boundp `(logbitp ,index ,bound))
      (:unbind `(progn (setf ,access nil ,bound (logandc2 ,bound ,(ash 1 index))) ,object)))))

(defun emit-record-slot-errors (build)
  ;; One slow path retains the complete condition/restart behavior. Repeating
  ;; RESTART-CASE in every class/slot branch bloats the host control-flow graph.
  (let ((object (gensym "RECORD")) (slot (gensym "SLOT")) (value (gensym "VALUE")))
    (emit-form build
      `(defun ,(closed-name build '%record-invalid-slot) (,object ,slot)
         (unless (or ,@(loop for description in (build-layouts build)
                            collect `(,(class-description-predicate description) ,object)))
           (error 'type-error :datum ,object
                  :expected-type '(or ,@(mapcar #'class-description-type (build-layouts build)))))
         (error 'simple-error
                :format-control "The slot ~S is missing from the object ~S."
                :format-arguments (list ,slot ,object))))
    (emit-form build
      `(defun ,(closed-name build '%record-unbound) (,object ,slot)
         (restart-case (error 'unbound-slot :instance ,object :name ,slot)
           (use-value (,value) ,value)
           (store-value (,value)
             (setf (,(closed-name build '%record-read) ,object ,slot) ,value)))))))

(defun emit-record-slot-dispatch (build operation)
  (let* ((name (record-operation-helper build operation))
         (object (gensym "RECORD")) (slot-name (gensym "SLOT")) (value (gensym "VALUE"))
         (slots (remove-duplicates
                 (loop for description in (build-layouts build)
                       append (mapcar #'slot-description-name (class-description-slots description)))))
         (arguments (if (eq operation :write) (list value object) (list object))))
    (dolist (slot slots)
      (let ((cases (loop for description in (build-layouts build)
                         for field = (find slot (class-description-slots description)
                                           :key #'slot-description-name)
                         when field collect
                           (list (class-description-type description)
                                 (class-description-predicate description)
                                 (slot-description-field field)
                                 (record-slot-body build description field operation object value)))))
        (push (list :name (record-slot-function build operation slot)
                    :operation operation :slot slot :arguments arguments
                    :invalid (closed-name build '%record-invalid-slot)
                    :object object :value value :cases cases)
              (build-slot-plans build))
        (emit-form build
          `(defun ,(record-slot-function build operation slot) ,arguments
             (cond
               ,@(loop for (type predicate field body) in cases
                       collect `((,predicate ,object) ,body))
               (t (,(closed-name build '%record-invalid-slot) ,object ',slot)))))))
    (emit-form
     build
     `(defun ,name ,(if (eq operation :write) (list value object slot-name) (list object slot-name))
        (unless (symbolp ,slot-name)
          (error 'type-error :datum ,slot-name :expected-type 'symbol))
        (case ,slot-name
          ,@(loop for slot in slots collect
                  `((,slot) (funcall #',(record-slot-function build operation slot) ,@arguments)))
          (otherwise (,(closed-name build '%record-invalid-slot) ,object ,slot-name)))))))

(defun emit-record-constructor (build description)
  (let ((args (gensym "INITARGS")) (object (gensym "RECORD"))
        (value (gensym "VALUE")) (presentp (gensym "PRESENT"))
        (lookup (closed-name build '%find-initarg)))
    (emit-form
     build
     `(defun ,(class-description-constructor description) (&rest ,args)
        (unless (evenp (length ,args))
          (error ',(closed-name build '%program-error)
                 :format-control "Odd number of initialization arguments."))
        ,@(loop for (key form) in (class-description-defaults description)
                collect
                `(unless (nth-value 1 (,lookup ,args '(,key)))
                   (setf ,args (append ,args (list ',key ,(rewrite-form build form :closed))))))
        (,(closed-name build '%check-initargs)
         ,args ',(remove-duplicates
                  (cons :allow-other-keys
                        (loop for slot in (class-description-slots description)
                              append (slot-description-initargs slot))))
         ,(closed-class-token-form build (class-description-name description)))
        (let ((,object (,(class-description-allocator description))))
          ,@(loop for slot in (class-description-slots description)
                  collect
                  `(multiple-value-bind (,value ,presentp)
                       (,lookup ,args ',(slot-description-initargs slot))
                     (cond (,presentp
                            (setf (,(closed-name build '%record-read) ,object ',(slot-description-name slot)) ,value))
                           ,@(when (slot-description-initform-p slot)
                               `((t (setf (,(closed-name build '%record-read) ,object ',(slot-description-name slot))
                                          ,(rewrite-form build (slot-description-initform slot) :closed))))))))
          ,object)))))

(defun emit-record-make-instance-binding (build)
  (let ((class (gensym "CLASS")) (initargs (gensym "INITARGS"))
        (descriptor (gensym "CLASS-DESCRIPTOR")))
    (emit-form
     build
     `(defun ,(record-make-instance-name build :closed) (,class &rest ,initargs)
        (let ((,descriptor (if (symbolp ,class)
                               (,(metadata-function-name build 'find-class :closed) ,class)
                               ,class)))
          (apply (,(closed-name build '%metadata-class-constructor) ,descriptor) ,initargs))))))

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
             `(defun ,(closed-name build '%find-initarg) (arguments keys)
                (loop for (key value) on arguments by #'cddr
                      when (member key keys :test #'eq) return (values value t)
                      finally (return (values nil nil)))))
  (let ((args (gensym "INITARGS")) (allowed (gensym "ALLOWED"))
        (class (gensym "CLASS")) (key (gensym "KEY")) (invalid (gensym "INVALID")))
    (emit-form
     build
     `(defun ,(closed-name build '%check-initargs) (,args ,allowed ,class)
        (unless (,(closed-name build '%find-initarg) ,args '(:allow-other-keys))
          (let ((,invalid
                  (loop for (,key) on ,args by #'cddr
                        unless (member ,key ,allowed :test #'eq) collect ,key)))
            (when ,invalid
              (error ',(closed-name build '%program-error) :format-control "Invalid initialization arguments ~S for ~S."
                     :format-arguments (list (nreverse ,invalid) ,class))))))))
  (emit-record-slot-errors build)
  (dolist (operation '(:read :write :boundp :unbind))
    (emit-record-slot-dispatch build operation))
  (dolist (description (build-layouts build))
    (emit-record-constructor build description))
  (emit-record-make-instance-binding build))

(defun record-type-mentioned-p (build type)
  (if (consp type)
      (some (lambda (part) (record-type-mentioned-p build part)) type)
      (member type (build-classes build))))

(defun record-operation-form (build form phase)
  "Return a replacement and true when this is an owned record operation.
Operands remain source forms for the shared lexical rewriter."
  (let ((operator (first form)))
    (case operator
      (make-instance
       (unless (build-classes build)
         (unsupported :external-construction "MAKE-INSTANCE needs an owned class universe."))
       ;; Direct and captured calls share the same replacement function.
       ;; Ordinary evaluation completes every operand before class lookup.
       (values `(,(record-make-instance-name build phase) ,@(rest form)) t))
      ((slot-value slot-boundp slot-makunbound)
       (if (eq phase :open) (values form t)
           (let* ((operation (ecase operator (slot-value :read) (slot-boundp :boundp)
                                                   (slot-makunbound :unbind)))
                  (slot (third form)))
             (values (if (and (quoted slot) (symbolp (second slot))
                              (known-record-slot-p build (second slot)))
                         `(,(record-slot-function build operation (second slot)) ,(second form))
                         `(,(record-operation-helper build operation) ,@(rest form))) t))))
      (typep
       (let ((type-form (third form)))
         (when (and (consp type-form) (eq (first type-form) 'quote)
                    (null (cddr type-form)) (record-type-mentioned-p build (second type-form)))
           (let ((type (second type-form)) (value (gensym "TYPE-VALUE")))
             (unless (record-slot-type-supported-p build type)
               (unsupported :record-type "Unsupported closed class type ~S." type))
             (values (if (eq phase :open)
                         `(typep ,(second form) ',(rewrite-type build type :open))
                         `(let ((,value ,(second form))) ,(closed-slot-type-test build type value))) t))))))))
