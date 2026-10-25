(in-package #:snowgrave)

;;; Validate the MOP boundary and materialize ordinary method functions.

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

(defun generic-open-function (build name)
  (fdefinition (if (member name '(initialize-instance shared-initialize))
                   name (open-name build name))))

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
    (make-lambda-shape :required (nreverse required) :optional (nreverse optional)
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

(defun validate-method-next-syntax (form)
  ;; This small profile admits only the original-argument continuation.
  ;; Conservatively reserve its spelling even in a nested local binding.
  (labels ((visit (node)
             (when (consp node)
               (cond ((eq (first node) 'quote) nil)
                     ((and (eq (first node) 'call-next-method) (rest node))
                      (unsupported :changed-next-method
                                   "Only direct zero-argument CALL-NEXT-METHOD is admitted."))
                     ((and (eq (first node) 'function) (eq (second node) 'call-next-method))
                      (unsupported :next-method-capture
                                   "Capturing CALL-NEXT-METHOD can bypass the original-argument continuation."))
                     (t (mapc #'visit node))))))
    (visit form)))

(defun validate-stock-miss-protocol (generic method)
  (dolist (baseline *stock-miss-methods*)
    (when (or method (eq (first baseline) 'no-applicable-method))
    (let* ((name (first baseline))
           (arguments (if (eq name 'no-applicable-method) (list generic)
                          (list generic method)))
           (applicable (cl:compute-applicable-methods (fdefinition name) arguments)))
      (unless (and (= (length applicable) 1)
                   (let ((saved (assoc (first applicable) (second baseline))))
                     (and saved (eq (closer-mop:method-function (first applicable)) (second saved)))))
        (unsupported :miss-protocol "~S has a replaced or extended miss protocol." name))))))

(defun validate-generic-methods (build generic gf)
  (unless (member (class-of gf) (list (find-class 'standard-generic-function)
                                    (find-class 'closer-mop:standard-generic-function)))
    (unsupported :generic-metaclass "~S is not a standard generic function." generic))
  ;; Method-combination metaobjects need not be EQ across MOP queries (ECL
  ;; returns fresh objects). The disposable cohort is defined from this owned
  ;; declaration, so validate its combination contract directly.
  (let* ((definition (find-if (lambda (form) (and (eq (first form) 'defgeneric)
                                                  (equal (second form) generic))) (build-forms build)))
         (option (assoc :method-combination (cdddr definition))))
    (when (and option (not (equal (rest option) '(standard))))
      (unsupported :method-combination "~S needs an unsupported custom method combination." generic)))
  (validate-stock-miss-protocol gf nil)
  (dolist (method (closer-mop:generic-function-methods gf))
    (unless (member (cl:method-qualifiers method) '(nil (:before) (:after) (:around)) :test #'equal)
      (unsupported :method-qualifiers "Unsupported qualifiers in ~S." generic))
    (dolist (specializer (closer-mop:method-specializers method))
      (when (typep specializer 'closer-mop:eql-specializer)
        (unsupported :eql-specializer "EQL-specialized ~S needs an identity partition." generic))
      (unless (or (eq specializer (find-class t))
                  (source-class-for-metaobject build specializer)
                  (and (typep specializer 'built-in-class)
                       (member (cl:class-name specializer)
                               (getf (build-declaration build) :universe))))
        (unsupported :specializer "~S has an undeclared or unsupported native specializer ~S."
                     generic (cl:class-name specializer))))
    (validate-stock-miss-protocol gf method))
  gf)

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
         (validate-method-next-syntax (cddr source))
         (multiple-value-bind (qualifiers lambda-list body) (method-parts source)
           (declare (ignore qualifiers))
           (multiple-value-bind (declarations executable) (body-parts body)
             (setf declarations (remove-if #'stringp declarations))
             (let* ((ordinary (permissive-method-lambda-list (ordinary-method-lambda-list lambda-list)))
                    (method-wrapper
                     `(lambda ,(call-abi-parameters abi)
                        (flet ((,next-name ()
                                 ,(or next (no-next-method-form generic (call-abi-list abi))))
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
        (t (unsupported :method-source "No owned body for a method of ~S." generic)))
      name)))

(defun emit-effective-source (build generic effective abi)
  "Replace MOP method leaves with ordinary calls; return emitted source."
  (labels ((walk (form)
             (cond ((atom form)
                    (when (typep form 'closer-mop:metaobject)
                      (unsupported :effective-metaobject "A method combination embeds a builder object."))
                    form)
                   ((eq (first form) 'quote)
                    (when (typep (second form) 'closer-mop:metaobject)
                      (unsupported :effective-metaobject "A method combination quotes a builder object."))
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
