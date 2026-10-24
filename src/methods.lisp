(in-package #:snowgrave)

;; The MOP supplies applicability and composition. This file only enumerates
;; a finite partition and replaces its method leaves with owned ordinary code.
(defparameter *stock-miss-methods*
  (loop for name in '(no-applicable-method no-next-method)
        collect (list name
                      (loop for method in (closer-mop:generic-function-methods (fdefinition name))
                            when (and (null (method-qualifiers method))
                                      (every (lambda (class)
                                               (member (class-name class)
                                                       '(t generic-function standard-generic-function method standard-method)))
                                             (closer-mop:method-specializers method)))
                              collect (list method (closer-mop:method-function method))))))

(defvar *method-source-cache* nil)

;; Bounded generic calls carry scalars and an optional supplied-prefix count.
;; A genuinely variable argument tail retains the ordinary list convention.
;; Both conventions preserve the original arguments across method bindings.
(defstruct method-call-abi arguments required optional-count list-parameter)

(defun make-generic-call-abi (shape)
  (if (or (getf shape :rest) (getf shape :keyp))
      (make-method-call-abi :list-parameter (gensym "ARGUMENTS"))
      (make-method-call-abi
       :required (length (getf shape :required))
       :arguments (loop repeat (+ (length (getf shape :required))
                                  (length (getf shape :optional))) collect (gensym "ARGUMENT"))
       :optional-count (when (getf shape :optional) (gensym "OPTIONAL-COUNT")))))

(defun call-abi-parameters (abi)
  (if (method-call-abi-list-parameter abi)
      (list (method-call-abi-list-parameter abi))
      (append (when (method-call-abi-optional-count abi)
                (list (method-call-abi-optional-count abi)))
              (method-call-abi-arguments abi))))

(defun call-abi-argument (abi index)
  (if (method-call-abi-list-parameter abi)
      `(nth ,index ,(method-call-abi-list-parameter abi))
      (nth index (method-call-abi-arguments abi))))

(defun call-abi-list (abi)
  "Materialize original arguments only for variable calls or exceptional paths."
  (or (method-call-abi-list-parameter abi)
      (let ((arguments (method-call-abi-arguments abi))
            (count (method-call-abi-optional-count abi)))
        (if count
            `(case ,count
               ,@(loop for supplied from 0 to (- (length arguments) (method-call-abi-required abi))
                       collect `(,supplied (list ,@(subseq arguments 0 (+ (method-call-abi-required abi) supplied))))))
            `(list ,@arguments)))))

(defun call-abi-lambda (abi lambda-form)
  (cond ((method-call-abi-list-parameter abi)
         `(apply (function ,lambda-form) ,(method-call-abi-list-parameter abi)))
        ((method-call-abi-optional-count abi)
         (let ((body (gensym "METHOD-BODY")) (arguments (method-call-abi-arguments abi)))
           ;; Define the method body once. Each arm supplies exactly the
           ;; original prefix, so defaults and supplied-p variables stay local
           ;; to each method, including repeated CALL-NEXT-METHOD invocations.
           `(flet ((,body ,@(rest lambda-form)))
              (case ,(method-call-abi-optional-count abi)
                ,@(loop for supplied from 0 to (- (length arguments) (method-call-abi-required abi))
                        collect `(,supplied (,body ,@(subseq arguments 0 (+ (method-call-abi-required abi) supplied)))))))))
        (t `(funcall (function ,lambda-form) ,@(method-call-abi-arguments abi)))))

(defun generic-open-function (build name)
  (fdefinition (if (member name '(initialize-instance shared-initialize))
                   name (open-name build name))))

(defun method-body-parts (body)
  (let ((documentation (when (and (stringp (first body)) (rest body)) (pop body))) (declarations nil))
    (loop while (and (consp (first body)) (eq (caar body) 'declare))
          do (push (pop body) declarations))
    (values documentation (nreverse declarations) body)))

(defun method-lambda-shape (lambda-list)
  (let ((mode :required) (required nil) (optional nil) (rest nil)
        (keys nil) (keyp nil) (allow nil))
    (dolist (item lambda-list)
      (cond ((eq item '&optional) (setf mode :optional))
            ((eq item '&rest) (setf mode :rest))
            ((eq item '&key) (setf mode :key keyp t))
            ((eq item '&allow-other-keys) (setf allow t))
            ((eq item '&aux) (setf mode :aux))
            ((eq mode :required) (push item required))
            ((eq mode :optional) (push item optional))
            ((eq mode :rest) (setf rest item mode :after-rest))
            ((eq mode :key)
             (let ((binding (if (consp item) (first item) item)))
               (push (if (consp binding) (first binding)
                         (intern (symbol-name binding) :keyword)) keys)))))
    (list :required (nreverse required) :optional (nreverse optional)
          :rest rest :keyp keyp :keys (nreverse keys) :allow allow)))

(defun permissive-method-lambda-list (lambda-list)
  ;; The generic validates the union of accepted keys. Each participating
  ;; ordinary method must then accept keys belonging to another method.
  (if (and (member '&key lambda-list) (not (member '&allow-other-keys lambda-list)))
      (let ((aux (position '&aux lambda-list)))
        (append (if aux (subseq lambda-list 0 aux) lambda-list)
                '(&allow-other-keys) (when aux (nthcdr aux lambda-list))))
      lambda-list))

(defun source-specializer-class (build name)
  (find-class (if (source-class-p build name) (open-name build name) name)))

(defun owned-method-source (build generic method)
  (find-if
   (lambda (form)
     (and (equal (second form) generic)
          (multiple-value-bind (qualifiers lambda-list body) (method-parts form)
            (declare (ignore body))
            (and (equal qualifiers (cl:method-qualifiers method))
                 (equal (loop for parameter in lambda-list
                              until (member parameter lambda-list-keywords)
                              for specializer = (if (consp parameter) (second parameter) t)
                              collect (and (symbolp specializer)
                                           (source-specializer-class build specializer)))
                        (closer-mop:method-specializers method))))))
   (build-method-sources build)))

(defun validate-method-next-syntax (build form)
  ;; This small profile admits only the original-argument continuation.
  ;; Conservatively reserve its spelling even in a nested local binding.
  (labels ((visit (node)
             (when (consp node)
               (cond ((eq (first node) 'quote) nil)
                     ((and (eq (first node) 'call-next-method) (rest node))
                      (unsupported build :changed-next-method
                                   "Only direct zero-argument CALL-NEXT-METHOD is admitted."))
                     ((and (eq (first node) 'function) (eq (second node) 'call-next-method))
                      (unsupported build :next-method-capture
                                   "Capturing CALL-NEXT-METHOD can bypass the original-argument continuation."))
                     (t (mapc #'visit node))))))
    (visit form)))

(defun validate-stock-miss-protocol (build generic method)
  (dolist (baseline *stock-miss-methods*)
    (when (or method (eq (first baseline) 'no-applicable-method))
    (let* ((name (first baseline))
           (arguments (if (eq name 'no-applicable-method) (list generic)
                          (list generic method)))
           (applicable (cl:compute-applicable-methods (fdefinition name) arguments)))
      (unless (and (= (length applicable) 1)
                   (let ((saved (assoc (first applicable) (second baseline))))
                     (and saved (eq (closer-mop:method-function (first applicable)) (second saved)))))
        (unsupported build :miss-protocol "~S has a replaced or extended miss protocol." name))))))

(defun validate-generic-methods (build generic gf)
  (unless (member (class-of gf) (list (find-class 'standard-generic-function)
                                    (find-class 'closer-mop:standard-generic-function)))
    (unsupported build :generic-metaclass "~S is not a standard generic function." generic))
  ;; Method-combination metaobjects need not be EQ across MOP queries (ECL
  ;; returns fresh objects). The disposable cohort is defined from this owned
  ;; declaration, so validate its combination contract directly.
  (let* ((definition (find-if (lambda (form) (and (eq (first form) 'defgeneric)
                                                  (equal (second form) generic))) (build-forms build)))
         (option (assoc :method-combination (cdddr definition))))
    (when (and option (not (equal (rest option) '(standard))))
      (unsupported build :method-combination "~S needs an unsupported custom method combination." generic)))
  (validate-stock-miss-protocol build gf nil)
  (dolist (method (closer-mop:generic-function-methods gf))
    (unless (member (cl:method-qualifiers method) '(nil (:before) (:after) (:around)) :test #'equal)
      (unsupported build :method-qualifiers "Unsupported qualifiers in ~S." generic))
    (dolist (specializer (closer-mop:method-specializers method))
      (when (typep specializer 'closer-mop:eql-specializer)
        (unsupported build :eql-specializer "EQL-specialized ~S needs an identity partition." generic))
      (unless (or (eq specializer (find-class t))
                  (source-class-for-metaobject build specializer)
                  (and (typep specializer 'built-in-class)
                       (member (cl:class-name specializer)
                               (getf (build-declaration build) :universe))))
        (unsupported build :specializer "~S has an undeclared or unsupported native specializer ~S."
                     generic (cl:class-name specializer))))
    (validate-stock-miss-protocol build gf method))
  gf)

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
          (unsupported build :native-partition "Overlapping native classes ~S and ~S need an explicit partition."
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

(defun no-next-method-form (build generic method arguments)
  (declare (ignore build method))
  `(error 'simple-error :format-control "No next method for ~S with arguments ~S."
          :format-arguments (list ',generic ,arguments)))

(defun emitted-method-function (build generic method next-methods abi)
  (let* ((key (list method next-methods))
         (existing (gethash key *method-source-cache*)))
    (when existing (return-from emitted-method-function existing))
    (let* ((name (fresh-name build "METHOD"))
           (next-name (gensym "CALL-NEXT-METHOD"))
           (nextp-name (gensym "NEXT-METHOD-P"))
           (next (when next-methods
                   (emit-effective-source build generic
                                          `(call-method ,(first next-methods) ,(rest next-methods))
                                          abi)))
           (source (owned-method-source build generic method)))
      (setf (gethash key *method-source-cache*) name)
      (push name (build-method-functions build))
      (cond
        ((typep method 'closer-mop:standard-accessor-method)
         (let* ((slot (closer-mop:slot-definition-name (closer-mop:accessor-method-slot-definition method)))
                (readerp (typep method 'closer-mop:standard-reader-method)))
           (emit-form build
                      `(defun ,name ,(call-abi-parameters abi)
                         ,(if readerp (record-reader-form build (call-abi-argument abi 0) slot)
                              (record-writer-form build (call-abi-argument abi 1) slot
                                                  (call-abi-argument abi 0)))))))
        (source
         (validate-method-next-syntax build (cddr source))
         (multiple-value-bind (qualifiers lambda-list body) (method-parts source)
           (declare (ignore qualifiers))
           (multiple-value-bind (documentation declarations executable) (method-body-parts body)
             (declare (ignore documentation))
             (let* ((ordinary (permissive-method-lambda-list (ordinary-method-lambda-list lambda-list)))
                    (method-wrapper
                      `(lambda ,(call-abi-parameters abi)
                         (flet ((,next-name ()
                                  ,(or next (no-next-method-form build generic method (call-abi-list abi))))
                                (,nextp-name () ,(not (null next-methods))))
                           ;; The continuation scope also surrounds optional
                           ;; and keyword initforms, as it does in DEFMETHOD.
                           ,(call-abi-lambda
                             abi (walk-source-form
                                  `(lambda ,ordinary ,@declarations
                                     (block ,(if (consp generic) (second generic) generic) ,@executable))
                                  nil
                                  (lambda (node context environment)
                                    (declare (ignore environment))
                                    (if (and (eq context :eval) (consp node)
                                             (member (first node) '(call-next-method next-method-p)))
                                        (cons (if (eq (first node) 'call-next-method) next-name nextp-name) (rest node))
                                        node))))))))
               (emit-form build `(defun ,name ,@(rest (rewrite-form build method-wrapper :closed))))))))
        (t (unsupported build :method-source "No owned body for a method of ~S." generic)))
      name)))

(defun emit-effective-source (build generic effective abi)
  "Replace MOP method leaves with ordinary calls; return emitted source."
  (labels ((walk (form)
             (cond ((atom form)
                    (when (typep form 'closer-mop:metaobject)
                      (unsupported build :effective-metaobject "A method combination embeds a builder object."))
                    form)
                   ((eq (first form) 'quote)
                    (when (typep (second form) 'closer-mop:metaobject)
                      (unsupported build :effective-metaobject "A method combination quotes a builder object."))
                    form)
                   ((eq (first form) 'call-method)
                    (let ((method (second form)) (next (third form)))
                      (if (and (consp method) (eq (first method) 'make-method))
                          (walk (second method))
                          `(,(emitted-method-function build generic method next abi)
                            ,@(call-abi-parameters abi)))))
                   (t (mapcar #'walk form)))))
    ;; Composition code and method bodies use the same closed binding rules.
    ;; Generated leaf calls already name ordinary output functions.
    (rewrite-form build (walk effective) :closed)))

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
               `(defun ,name (,@required ,@(when optional (cons '&optional optional))
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

(defun emit-one-generic (build generic)
  (let* ((gf (validate-generic-methods build generic (generic-open-function build generic)))
         (methods (closer-mop:generic-function-methods gf))
         (shape (method-lambda-shape (closer-mop:generic-function-lambda-list gf)))
         (required (length (getf shape :required)))
         (axes (loop for position below required collect (generic-axis-cuts build methods position)))
         (abi (make-generic-call-abi shape))
         (arguments (method-call-abi-list-parameter abi))
         (overflow (unless arguments (gensym "EXCESS-ARGUMENTS")))
         (supplied (loop repeat (length (getf shape :optional)) collect (gensym "SUPPLIED")))
         (cell-index (gensym "CELL"))
         (rows
           (loop for cell in (method-cartesian-product axes) collect
             (multiple-value-bind (applicable certainp)
                 (closer-mop:compute-applicable-methods-using-classes gf (mapcar #'third cell))
               (unless certainp
                 (unsupported build :method-applicability "The MOP cannot establish class-only applicability for ~S." generic))
               (list cell applicable))))
         (*method-source-cache* (make-hash-table :test #'equal))
         (groups nil) (clauses nil))
    ;; Many exact class tuples have the same ordered method list. Materialize
    ;; each effective method once and classify each argument once per call.
    ;; A giant repeated COND otherwise makes the host compiler's control-flow
    ;; graph grow with every duplicate body and every missing-method cell.
    (loop for row in rows for index from 0
          for applicable = (second row)
          when applicable
            do (let ((group (assoc applicable groups :test #'equal)))
                 (if group (push index (cdr group))
                     (push (list applicable index) groups))))
    (dolist (group (nreverse groups))
      (let ((applicable (car group)))
        (multiple-value-bind (effective options)
            (effective-method-source gf applicable)
          (when options
            (unsupported build :effective-options "~S returned unsupported effective-method options." generic))
          (push `(,(nreverse (cdr group))
                  ,(if arguments
                       (generic-validator-form build gf applicable arguments)
                       `(when ,overflow
                          (error ',(record-helper-name build '%program-error)
                                 :format-control "Too many arguments for closed generic ~S."
                                 :format-arguments (list ',generic))))
                  ,(emit-effective-source build generic effective abi))
                clauses))))
    (push (list :name (closed-name build generic) :source generic
                :required required :optional (length (getf shape :optional))
                :variable-tail (not (null arguments))
                :arguments (method-call-abi-arguments abi)
                :optional-count (method-call-abi-optional-count abi)
                :overflow overflow
                :axes (mapcar (lambda (axis)
                                (mapcar (lambda (cut)
                                          (list (first cut)
                                                (if (eq (first cut) :record)
                                                    (class-description-type (find-record-class build (second cut)))
                                                    (second cut)))) axis)) axes)
                :clauses (reverse clauses))
          (build-generic-plans build))
    (emit-form build
               `(defun ,(closed-name build generic)
                    ,(if arguments `(&rest ,arguments)
                         (append (subseq (method-call-abi-arguments abi) 0 required)
                                 (when supplied
                                   `(&optional ,@(loop for variable in (nthcdr required (method-call-abi-arguments abi))
                                                       for present in supplied collect `(,variable nil ,present))))
                                 ;; Preserve applicability-before-excess-arity.
                                 ;; Valid bounded calls have an empty tail.
                                 `(&rest ,overflow)))
                  ,@(when (and arguments (plusp required))
                      `((when (< (length ,arguments) ,required)
                          (error ',(record-helper-name build '%program-error)
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
                      ,@(nreverse clauses)
                      (otherwise ,(no-applicable-method-form
                                   build generic (if arguments arguments
                                                     `(append ,(call-abi-list abi) ,overflow))))))))))

(defun emit-generics (build)
  (dolist (generic (build-generics build)) (emit-one-generic build generic)))
