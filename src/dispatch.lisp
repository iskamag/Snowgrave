(in-package #:snowgrave)

;;; Partition dispatch domains and share one effective body per ordered method list.

(defun native-cuts-disjoint-p (left right)
  (multiple-value-bind (answer certainp)
      (subtypep `(and ,(cl:class-name left) ,(cl:class-name right)) nil)
    (and certainp answer)))

(defun native-class-subtype-p (left right)
  (member right (closer-mop:class-precedence-list left)))

(defun generic-axis-cuts (build methods position)
  (let* ((specializers (remove-duplicates
                       (mapcar (lambda (method) (nth position (closer-mop:method-specializers method))) methods)))
         (native (remove-if (lambda (class) (or (eq class (find-class t))
                                               (source-class-for-metaobject build class))) specializers)))
    (when (every (lambda (class) (eq class (find-class t))) specializers)
      (return-from generic-axis-cuts (list (make-dispatch-cut :kind :any :type t :class (find-class t)))))
    ;; Nested or disjoint native cuts have an exact nominal representative.
    ;; An unresolved intersection would need another cell, never a sample.
    (loop for tail on native do
      (dolist (other (rest tail))
        (unless (or (native-class-subtype-p (first tail) other)
                    (native-class-subtype-p other (first tail))
                    (native-cuts-disjoint-p (first tail) other))
          (unsupported :native-partition "Overlapping native classes ~S and ~S need an explicit partition."
                       (cl:class-name (first tail)) (cl:class-name other)))))
    (setf native (stable-sort native #'> :key (lambda (class) (length (closer-mop:class-precedence-list class)))))
    (append (mapcar (lambda (name) (make-dispatch-cut :kind :record :type name :class (source-specializer-class build name)))
                    (build-classes build))
            (loop for tail on native for index from 0
                  collect (make-dispatch-cut :kind :native :type (cl:class-name (first tail)) :class (first tail)
                                     :excluded (mapcar #'cl:class-name (subseq native 0 index))))
            (list (make-dispatch-cut :kind :other :type t :class (find-class t)
                                     :excluded (mapcar #'cl:class-name native))))))

(defun axis-cut-test (build cut value)
  (case (dispatch-cut-kind cut)
    (:any t)
    (:record (closed-exact-class-test build (dispatch-cut-type cut) value))
    (otherwise
     `(and (not (or ,@(mapcar (lambda (name) (closed-exact-class-test build name value))
                              (build-classes build))))
           ,@(when (eq (dispatch-cut-kind cut) :native) `((typep ,value ',(dispatch-cut-type cut))))
           ,@(when (dispatch-cut-excluded cut) `((not (or ,@(mapcar (lambda (name) `(typep ,value ',name))
                                                    (dispatch-cut-excluded cut))))))))))

(defun method-cartesian-product (axes)
  (if (null axes) (list nil)
      (loop for item in (first axes) append
        (loop for tail in (method-cartesian-product (rest axes)) collect (cons item tail)))))

(defun emit-miss-path (build)
  ;; One shared miss implementation instead of a copy per dispatcher.
  (let ((generic (gensym "GENERIC")) (arguments (gensym "ARGUMENTS"))
        (dispatcher (gensym "DISPATCHER")))
    (emit-form
     build
     `(defun ,(closed-name build '%record-no-applicable) (,generic ,arguments ,dispatcher)
        (restart-case
            (error 'simple-error :format-control "No applicable method for ~S with arguments ~S."
                   :format-arguments (list ,generic ,arguments))
          (retry () :report "Retry the closed generic function."
            (apply ,dispatcher ,arguments)))))))

(defun no-applicable-method-form (build generic arguments)
  `(,(closed-name build '%record-no-applicable) ',generic ,arguments
    #',(closed-name build generic)))

(defun no-next-method-form (generic arguments)
  `(error 'simple-error :format-control "No next method for ~S with arguments ~S."
          :format-arguments (list ',generic ,arguments)))

(defun generic-validator-form (build gf applicable arguments)
  (let* ((shape (method-lambda-shape (closer-mop:generic-function-lambda-list gf)))
         (method-shapes (mapcar (lambda (method) (method-lambda-shape (closer-mop:method-lambda-list method))) applicable))
         (keys (remove-duplicates (append (lambda-shape-keys shape)
                                          (loop for item in method-shapes append (lambda-shape-keys item)))))
         (allow (or (lambda-shape-allow shape) (some #'lambda-shape-allow method-shapes)))
         (required (loop repeat (length (lambda-shape-required shape)) collect (gensym "REQUIRED")))
         (optional (loop repeat (length (lambda-shape-optional shape)) collect (gensym "OPTIONAL")))
         (rest (when (or (lambda-shape-rest shape) (lambda-shape-keyp shape)) (gensym "REST")))
         (key-variables (mapcar (lambda (key) (list (list key (gensym "KEY")))) keys))
         (variables (append required optional (when rest (list rest))
                            (when (lambda-shape-keyp shape) (mapcar #'cadar key-variables))))
         (name (fresh-name build "ARGUMENTS")))
    (emit-form build
               `(defun ,name (,@required
                             ,@(when optional (cons '&optional optional))
                             ,@(when rest (list '&rest rest))
                             ,@(when (lambda-shape-keyp shape) (cons '&key key-variables))
                             ,@(when (and (lambda-shape-keyp shape) allow) '(&allow-other-keys)))
                  ,@(when variables `((declare (ignore ,@variables))))
                  (values)))
    `(apply #',name ,arguments)))

(defun axis-strides (axes)
  "Row-major stride per axis in the flattened cell index."
  (loop for tail on axes
        collect (apply #'* (mapcar #'length (rest tail)))))

(defun method-axis-index-form (build axis argument)
  ;; Exact owned classes and admitted native cuts partition one argument.
  ;; The final remainder is exhaustive after all preceding tests fail.
  (if (rest axis)
      `(cond ,@(loop for tail on axis for index from 0
                     collect `(,(if (rest tail) (axis-cut-test build (first tail) argument) t)
                                ,index)))
      ;; A single cut accepts every value, so the index is constant.
      0))

(defun generic-method-groups (build generic gf axes)
  "Group cell indices by the MOP's ordered applicable-method list."
  (let ((groups nil))
    (loop for cell in (method-cartesian-product axes)
          for index from 0
          do (multiple-value-bind (applicable certainp)
                 (closer-mop:compute-applicable-methods-using-classes gf (mapcar #'dispatch-cut-class cell))
               (unless certainp
                 (unsupported :method-applicability
                              "The MOP cannot establish class-only applicability for ~S." generic))
               (when applicable
                 (let ((group (assoc applicable groups :test #'equal)))
                   (if group (push index (cdr group))
                       (push (list applicable index) groups))))))
    (nreverse groups)))

(defun generic-dispatch-clauses (build generic gf axes abi overflow)
  ;; Share each effective body across all cells with the same method list.
  ;; Repeating those bodies makes the host compiler's control-flow graph grow
  ;; unnecessarily, especially when most cells have no applicable method.
  (loop for (applicable . indices) in (generic-method-groups build generic gf axes)
        collect
        (multiple-value-bind (effective options) (effective-method-source build generic gf applicable)
          (when options
            (unsupported :effective-options
                         "~S returned unsupported effective-method options." generic))
          (make-generic-clause
           :indices (nreverse indices)
           :body (list
                  (if (method-call-abi-list-parameter abi)
                      (generic-validator-form build gf applicable (method-call-abi-list-parameter abi))
                      `(when ,overflow
                         (error ',(closed-name build '%program-error)
                                :format-control "Too many arguments for closed generic ~S."
                                :format-arguments (list ',generic))))
                  (emit-effective-source build generic effective abi))))))

(defun project-dispatch-domains (build axes)
  ;; Projection is explicit: class metaobjects stay in builder-only cuts.
  (mapcar (lambda (axis)
            (mapcar (lambda (cut)
                      (make-dispatch-domain
                       :kind (dispatch-cut-kind cut)
                       :type (if (eq (dispatch-cut-kind cut) :record)
                                 (class-description-type (find-record-class build (dispatch-cut-type cut)))
                                 (dispatch-cut-type cut))))
                    axis))
          axes))

(defun generic-entry-lambda-list (abi supplied overflow)
  (if (method-call-abi-list-parameter abi)
      `(&rest ,(method-call-abi-list-parameter abi))
      (let ((required (method-call-abi-required abi))
            (arguments (method-call-abi-arguments abi)))
        (append (subseq arguments 0 required)
                (when supplied
                  `(&optional ,@(loop for variable in (nthcdr required arguments)
                                      for present in supplied collect `(,variable nil ,present))))
                ;; Preserve applicability-before-excess-arity. Valid bounded
                ;; calls have an empty tail.
                `(&rest ,overflow)))))

(defun generic-cell-index-form (build axes abi)
  "Flattened cell index, computed directly instead of by repeated SETF."
  (let ((forms (loop for axis in axes for position from 0
                     collect (method-axis-index-form
                              build axis (call-abi-argument abi position)))))
    (cond ((null forms) 0)
          ((null (cdr forms)) (car forms))
          (t (cons '+ (loop for form in forms
                            for stride in (axis-strides axes)
                            collect (if (= stride 1) form (list '* stride form))))))))

(defun generic-entry-form (build generic shape axes abi overflow clauses)
  (let ((arguments (method-call-abi-list-parameter abi))
        (required (length (lambda-shape-required shape)))
        (supplied (loop repeat (length (lambda-shape-optional shape)) collect (gensym "SUPPLIED")))
        (count (method-call-abi-optional-count abi))
        (cell-index (gensym "CELL")))
    `(defun ,(closed-name build generic) ,(generic-entry-lambda-list abi supplied overflow)
       ,@(when (and arguments (plusp required))
           (list `(when (< (length ,arguments) ,required)
                    (error ',(closed-name build '%program-error)
                           :format-control "Too few arguments for closed generic ~S: ~S."
                           :format-arguments (list ',generic ,arguments)))))
       (let (,@(when count
                 (list `(,count (cond ,@(loop for present in (reverse supplied)
                                              for seen downfrom (length supplied)
                                              collect `(,present ,seen))
                                      (t 0))))))
         (let ((,cell-index ,(generic-cell-index-form build axes abi)))
           (case ,cell-index
             ,@(mapcar (lambda (clause)
                         (cons (generic-clause-indices clause) (generic-clause-body clause)))
                       clauses)
             (otherwise
              ,(no-applicable-method-form
                build generic (if arguments arguments `(append ,(call-abi-list abi) ,overflow))))))))))

(defun emit-one-generic (build generic)
  (let* ((gf (validate-generic-methods build generic (generic-open-function build generic)))
         (methods (closer-mop:generic-function-methods gf))
         (shape (method-lambda-shape (closer-mop:generic-function-lambda-list gf)))
         (required (length (lambda-shape-required shape)))
         (axes (loop for position below required collect (generic-axis-cuts build methods position)))
         (abi (make-generic-call-abi shape))
         (overflow (unless (method-call-abi-list-parameter abi) (gensym "EXCESS-ARGUMENTS")))
         (*method-source-cache* (make-hash-table :test #'equal))
         (clauses (generic-dispatch-clauses build generic gf axes abi overflow)))
    (push (make-generic-plan :name (closed-name build generic) :source generic
                :required required :optional (length (lambda-shape-optional shape))
                :variable-tail (not (null (method-call-abi-list-parameter abi)))
                :arguments (method-call-abi-arguments abi)
                :optional-count (method-call-abi-optional-count abi)
                :overflow overflow :axes (project-dispatch-domains build axes) :clauses clauses)
          (build-generic-plans build))
    (emit-form build (generic-entry-form build generic shape axes abi overflow clauses))))

(defun emit-generics (build)
  (when (build-generics build) (emit-miss-path build))
  (dolist (generic (build-generics build)) (emit-one-generic build generic)))
