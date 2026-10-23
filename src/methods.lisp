(in-package #:snowgrave)

;; The MOP supplies applicability and composition. This file only enumerates
;; a finite partition and replaces its method leaves with owned ordinary code.
(defparameter *stock-miss-methods*
  (loop for (name specializers) in
        '((no-applicable-method (t))
          (no-next-method (standard-generic-function standard-method)))
        for method = (find-method (fdefinition name) nil (mapcar #'find-class specializers))
        collect (list name method (sb-mop:method-function method))))

(defvar *method-source-cache* nil)

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
            (and (equal qualifiers (sb-mop:method-qualifiers method))
                 (equal (loop for parameter in lambda-list
                              until (member parameter lambda-list-keywords)
                              for specializer = (if (consp parameter) (second parameter) t)
                              collect (and (symbolp specializer)
                                           (source-specializer-class build specializer)))
                        (sb-mop:method-specializers method))))))
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
           (applicable (sb-mop:compute-applicable-methods (fdefinition name) arguments)))
      (unless (and (= (length applicable) 1)
                   (eq (first applicable) (second baseline))
                   (eq (sb-mop:method-function (first applicable)) (third baseline)))
        (unsupported build :miss-protocol "~S has a replaced or extended miss protocol." name))))))

(defun validate-generic-methods (build generic gf)
  (unless (eq (class-of gf) (find-class 'standard-generic-function))
    (unsupported build :generic-metaclass "~S is not a standard generic function." generic))
  (unless (eq (sb-mop:generic-function-method-combination gf)
              (sb-mop:find-method-combination gf 'standard nil))
    (unsupported build :method-combination "~S needs an unsupported custom method combination." generic))
  (validate-stock-miss-protocol build gf nil)
  (dolist (method (sb-mop:generic-function-methods gf))
    (unless (member (sb-mop:method-qualifiers method) '(nil (:before) (:after) (:around)) :test #'equal)
      (unsupported build :method-qualifiers "Unsupported qualifiers in ~S." generic))
    (dolist (specializer (sb-mop:method-specializers method))
      (when (typep specializer 'sb-mop:eql-specializer)
        (unsupported build :eql-specializer "EQL-specialized ~S needs an identity partition." generic))
      (unless (or (eq specializer (find-class t))
                  (source-class-for-metaobject build specializer)
                  (and (typep specializer 'built-in-class)
                       (member (sb-mop:class-name specializer)
                               (getf (build-declaration build) :universe))))
        (unsupported build :specializer "~S has an undeclared or unsupported native specializer ~S."
                     generic (sb-mop:class-name specializer))))
    (validate-stock-miss-protocol build gf method))
  gf)

(defun native-cuts-disjoint-p (left right)
  (multiple-value-bind (answer certainp)
      (subtypep `(and ,(sb-mop:class-name left) ,(sb-mop:class-name right)) nil)
    (and certainp answer)))

(defun native-class-subtype-p (left right)
  (member right (sb-mop:class-precedence-list left)))

(defun generic-axis-cuts (build methods position)
  (let* ((specializers (remove-duplicates
                       (mapcar (lambda (method) (nth position (sb-mop:method-specializers method))) methods)))
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
                       (sb-mop:class-name (first tail)) (sb-mop:class-name other)))))
    (setf native (stable-sort native #'> :key (lambda (class) (length (sb-mop:class-precedence-list class)))))
    (append (mapcar (lambda (name) (list :record name (source-specializer-class build name)))
                    (build-classes build))
            (loop for tail on native for index from 0
                  collect (list :native (sb-mop:class-name (first tail)) (first tail)
                                (mapcar #'sb-mop:class-name (subseq native 0 index))))
            (list (list :other t (find-class t) (mapcar #'sb-mop:class-name native))))))

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
       (error 'sb-pcl::no-applicable-method-error
              :generic-function #',(closed-name build generic) :args ,arguments)
     (sb-ext:retry () :report "Retry the closed generic function."
       (apply #',(closed-name build generic) ,arguments))))

(defun no-next-method-form (build generic method arguments)
  `(error 'sb-pcl::no-next-method-error
          :generic-function #',(closed-name build generic) :args ,arguments
          :method ',(list :method generic (sb-mop:method-qualifiers method)
                          (mapcar (lambda (class) (or (source-class-for-metaobject build class)
                                                     (sb-mop:class-name class)))
                                  (sb-mop:method-specializers method)))))

(defun emitted-method-function (build generic method next-methods)
  (let* ((key (list method next-methods))
         (existing (gethash key *method-source-cache*)))
    (when existing (return-from emitted-method-function existing))
    (let* ((name (fresh-name build "METHOD")) (arguments (gensym "ARGUMENTS"))
           (next (when next-methods
                   (emit-effective-source build generic
                                          `(call-method ,(first next-methods) ,(rest next-methods))
                                          arguments)))
           (source (owned-method-source build generic method)))
      (setf (gethash key *method-source-cache*) name)
      (cond
        ((typep method 'sb-mop:standard-accessor-method)
         (let* ((slot (sb-mop:slot-definition-name (sb-mop:accessor-method-slot-definition method)))
                (readerp (typep method 'sb-mop:standard-reader-method)))
           (emit-form build
                      `(defun ,name (,arguments)
                         ,(if readerp (record-reader-form build `(first ,arguments) slot)
                              (record-writer-form build `(second ,arguments) slot `(first ,arguments)))))))
        (source
         (validate-method-next-syntax build (cddr source))
         (multiple-value-bind (qualifiers lambda-list body) (method-parts source)
           (declare (ignore qualifiers))
           (multiple-value-bind (documentation declarations executable) (method-body-parts body)
             (declare (ignore documentation))
             (let* ((ordinary (permissive-method-lambda-list (ordinary-method-lambda-list lambda-list)))
                    (method-wrapper
                      `(lambda (,arguments)
                         (declare (sb-ext:disable-package-locks call-next-method next-method-p))
                         (flet ((call-next-method ()
                                  ,(or next (no-next-method-form build generic method arguments)))
                                (next-method-p () ,(not (null next-methods))))
                           ;; The continuation scope also surrounds optional
                           ;; and keyword initforms, as it does in DEFMETHOD.
                           (apply (function (lambda ,ordinary ,@declarations
                                              (block ,(if (consp generic) (second generic) generic)
                                                ,@executable)))
                                  ,arguments)))))
               (emit-form build `(defun ,name ,@(rest (rewrite-form build method-wrapper :closed))))))))
        (t (unsupported build :method-source "No owned body for a method of ~S." generic)))
      name)))

(defun emit-effective-source (build generic effective arguments-form)
  "Replace MOP method leaves with ordinary calls; return emitted source."
  (labels ((walk (form)
             (cond ((atom form)
                    (when (typep form 'sb-mop:metaobject)
                      (unsupported build :effective-metaobject "A method combination embeds a builder object."))
                    form)
                   ((eq (first form) 'quote)
                    (when (typep (second form) 'sb-mop:metaobject)
                      (unsupported build :effective-metaobject "A method combination quotes a builder object."))
                    form)
                   ((eq (first form) 'call-method)
                    (let ((method (second form)) (next (third form)))
                      (if (and (consp method) (eq (first method) 'make-method))
                          (walk (second method))
                          `(,(emitted-method-function build generic method next) ,arguments-form))))
                   (t (mapcar #'walk form)))))
    ;; Composition code and method bodies use the same closed binding rules.
    ;; Generated leaf calls already name ordinary output functions.
    (rewrite-form build (walk effective) :closed)))

(defun generic-validator-form (build gf applicable arguments)
  (let* ((shape (method-lambda-shape (sb-mop:generic-function-lambda-list gf)))
         (method-shapes (mapcar (lambda (method) (method-lambda-shape (sb-mop:method-lambda-list method))) applicable))
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
         (methods (sb-mop:generic-function-methods gf))
         (required (length (getf (method-lambda-shape (sb-mop:generic-function-lambda-list gf)) :required)))
         (axes (loop for position below required collect (generic-axis-cuts build methods position)))
         (arguments (gensym "ARGUMENTS"))
         (cell-index (gensym "CELL"))
         (rows
           (loop for cell in (method-cartesian-product axes) collect
             (multiple-value-bind (applicable certainp)
                 (sb-mop:compute-applicable-methods-using-classes gf (mapcar #'third cell))
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
            (sb-mop:compute-effective-method
             gf (sb-mop:generic-function-method-combination gf) applicable)
          (when options
            (unsupported build :effective-options "~S returned unsupported effective-method options." generic))
          (push `(,(nreverse (cdr group))
                  ,(generic-validator-form build gf applicable arguments)
                  ,(emit-effective-source build generic effective arguments))
                clauses))))
    (emit-form build
               `(defun ,(closed-name build generic) (&rest ,arguments)
                  ,@(when (plusp required)
                      `((when (< (length ,arguments) ,required)
                          (error 'sb-int:simple-program-error
                                 :format-control "Too few arguments for closed generic ~S: ~S."
                                 :format-arguments (list ',generic ,arguments)))))
                  (let ((,cell-index 0))
                    ,@(loop for axis in axes for index from 0
                            collect `(setf ,cell-index
                                           (+ (* ,cell-index ,(length axis))
                                              ,(method-axis-index-form build axis `(nth ,index ,arguments)))))
                    (case ,cell-index
                      ,@(nreverse clauses)
                      (otherwise ,(no-applicable-method-form build generic arguments))))))
    (list :name generic :code-name (closed-name build generic)
          :lambda-list (sb-mop:generic-function-lambda-list gf)
          :cells (loop for row in rows
                       collect (list :classes (mapcar #'second (first row))
                                     :methods (mapcar (lambda (method)
                                                       (list :qualifiers (sb-mop:method-qualifiers method)
                                                             :specializers (mapcar (lambda (class)
                                                                                     (or (source-class-for-metaobject build class)
                                                                                         (sb-mop:class-name class)))
                                                                                   (sb-mop:method-specializers method))))
                                                     (second row)))))))

(defun emit-generics (build)
  (mapcar (lambda (generic) (emit-one-generic build generic)) (build-generics build)))
