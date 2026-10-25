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
      (return-from generic-axis-cuts (list (list :any t (find-class t)))))
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
    (append (mapcar (lambda (name) (list :record name (source-specializer-class build name)))
                    (build-classes build))
            (loop for tail on native for index from 0
                  collect (list :native (cl:class-name (first tail)) (first tail)
                                (mapcar #'cl:class-name (subseq native 0 index))))
            (list (list :other t (find-class t) (mapcar #'cl:class-name native))))))

(defun axis-cut-test (build cut value)
  (case (first cut)
    (:any t)
    (:record (closed-exact-class-test build (second cut) value))
    (otherwise
     `(and (not (or ,@(mapcar (lambda (name) (closed-exact-class-test build name value))
                              (build-classes build))))
           ,@(when (eq (first cut) :native) `((typep ,value ',(second cut))))
           ,@(when (fourth cut) `((not (or ,@(mapcar (lambda (name) `(typep ,value ',name))
                                                    (fourth cut))))))))))

(defun method-cartesian-product (axes)
  (if (null axes) (list nil)
      (loop for item in (first axes) append
        (loop for tail in (method-cartesian-product (rest axes)) collect (cons item tail)))))

(defun no-applicable-method-form (build generic arguments)
  `(restart-case
       (error 'simple-error :format-control "No applicable method for ~S with arguments ~S."
              :format-arguments (list ',generic ,arguments))
     (retry () :report "Retry the closed generic function."
       (apply #',(closed-name build generic) ,arguments))))

(defun no-next-method-form (generic arguments)
  `(error 'simple-error :format-control "No next method for ~S with arguments ~S."
          :format-arguments (list ',generic ,arguments)))

(defun generic-validator-form (build gf applicable arguments)
  (let* ((shape (method-lambda-shape (closer-mop:generic-function-lambda-list gf)))
         (method-shapes (mapcar (lambda (method) (method-lambda-shape (closer-mop:method-lambda-list method))) applicable))
         (keys (remove-duplicates (append (getf shape :keys)
                                          (loop for item in method-shapes append (getf item :keys)))))
         (allow (or (getf shape :allow) (some (lambda (item) (getf item :allow)) method-shapes)))
         (required (loop repeat (length (getf shape :required)) collect (gensym "REQUIRED")))
         (optional (loop repeat (length (getf shape :optional)) collect (gensym "OPTIONAL")))
         (rest (when (or (getf shape :rest) (getf shape :keyp)) (gensym "REST")))
         (key-variables (mapcar (lambda (key) (list (list key (gensym "KEY")))) keys))
         (variables (append required optional (when rest (list rest))
                            (when (getf shape :keyp) (mapcar #'cadar key-variables))))
         (name (fresh-name build "ARGUMENTS")))
    (emit-form build
               `(defun ,name (,@required
                             ,@(when optional (cons '&optional optional))
                             ,@(when rest (list '&rest rest))
                             ,@(when (getf shape :keyp) (cons '&key key-variables))
                             ,@(when (and (getf shape :keyp) allow) '(&allow-other-keys)))
                  ,@(when variables `((declare (ignore ,@variables))))
                  (values)))
    `(apply #',name ,arguments)))

(defun method-axis-index-form (build axis argument)
  ;; Exact owned classes and admitted native cuts partition one argument.
  ;; The final remainder is exhaustive after all preceding tests fail.
  `(cond ,@(loop for tail on axis for index from 0
                 collect `(,(if (rest tail) (axis-cut-test build (first tail) argument) t)
                            ,index))))

(defun generic-method-groups (build generic gf axes)
  "Group cell indices by the MOP's ordered applicable-method list."
  (let ((groups nil))
    (loop for cell in (method-cartesian-product axes)
          for index from 0
          do (multiple-value-bind (applicable certainp)
                 (closer-mop:compute-applicable-methods-using-classes gf (mapcar #'third cell))
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
        (multiple-value-bind (effective options) (effective-method-source gf applicable)
          (when options
            (unsupported :effective-options
                         "~S returned unsupported effective-method options." generic))
          `(,(nreverse indices)
            ,(if (method-call-abi-list-parameter abi)
                 (generic-validator-form build gf applicable (method-call-abi-list-parameter abi))
                 `(when ,overflow
                    (error ',(closed-name build '%program-error)
                           :format-control "Too many arguments for closed generic ~S."
                           :format-arguments (list ',generic))))
            ,(emit-effective-source build generic effective abi)))))

(defun generic-plan-axes (build axes)
  ;; Retained specialization recipes contain source types, never MOP objects.
  (mapcar (lambda (axis)
            (mapcar (lambda (cut)
                      (list (first cut)
                            (if (eq (first cut) :record)
                                (class-description-type (find-record-class build (second cut)))
                                (second cut))))
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

(defun generic-entry-form (build generic shape axes abi overflow clauses)
  (let ((arguments (method-call-abi-list-parameter abi))
        (required (length (getf shape :required)))
        (supplied (loop repeat (length (getf shape :optional)) collect (gensym "SUPPLIED")))
        (cell-index (gensym "CELL")))
    `(defun ,(closed-name build generic) ,(generic-entry-lambda-list abi supplied overflow)
       ,@(when (and arguments (plusp required))
           `((when (< (length ,arguments) ,required)
               (error ',(closed-name build '%program-error)
                      :format-control "Too few arguments for closed generic ~S: ~S."
                      :format-arguments (list ',generic ,arguments)))))
       (let ((,cell-index 0)
             ,@(when (method-call-abi-optional-count abi)
                 `((,(method-call-abi-optional-count abi)
                    (cond ,@(loop for present in (reverse supplied)
                                  for count downfrom (length supplied) collect `(,present ,count))
                          (t 0))))))
         ,@(loop for axis in axes for index from 0
                 collect `(setf ,cell-index
                                (+ (* ,cell-index ,(length axis))
                                   ,(method-axis-index-form build axis (call-abi-argument abi index)))))
         (case ,cell-index
           ,@clauses
           (otherwise ,(no-applicable-method-form
                        build generic (if arguments arguments
                                          `(append ,(call-abi-list abi) ,overflow)))))))))

(defun emit-one-generic (build generic)
  (let* ((gf (validate-generic-methods build generic (generic-open-function build generic)))
         (methods (closer-mop:generic-function-methods gf))
         (shape (method-lambda-shape (closer-mop:generic-function-lambda-list gf)))
         (required (length (getf shape :required)))
         (axes (loop for position below required collect (generic-axis-cuts build methods position)))
         (abi (make-generic-call-abi shape))
         (overflow (unless (method-call-abi-list-parameter abi) (gensym "EXCESS-ARGUMENTS")))
         (*method-source-cache* (make-hash-table :test #'equal))
         (clauses (generic-dispatch-clauses build generic gf axes abi overflow)))
    (push (list :name (closed-name build generic) :source generic
                :required required :optional (length (getf shape :optional))
                :variable-tail (not (null (method-call-abi-list-parameter abi)))
                :arguments (method-call-abi-arguments abi)
                :optional-count (method-call-abi-optional-count abi)
                :overflow overflow :axes (generic-plan-axes build axes) :clauses clauses)
          (build-generic-plans build))
    (emit-form build (generic-entry-form build generic shape axes abi overflow clauses))))

(defun emit-generics (build)
  (dolist (generic (build-generics build)) (emit-one-generic build generic)))
