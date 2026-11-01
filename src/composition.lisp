(in-package #:snowgrave)

;;; The MOP may compile its effective method before returning it. Capture the
;;; source at the standard DEFINE-METHOD-COMBINATION boundary instead of
;;; inspecting a host-specific effective-method function or compiler closure.
(defvar *composition-source* :inactive)

(defun source-method-combination (build generic)
  (let* ((definition (find-source-definition build 'defgeneric generic))
         (specification (or (rest (assoc :method-combination (cdddr definition))) '(standard)))
         (name (first specification))
         (order (if (rest specification) (second specification) :most-specific-first)))
    (if (equal specification '(standard)) specification
        (let ((source (find-source-definition build 'define-method-combination name)))
          (unless (and source (<= (length specification) 2)
                       (member order
                               '(:most-specific-first :most-specific-last)))
            (unsupported :method-combination "~S needs an owned short method combination." generic))
          (list 'source-short name (getf (cddr source) :operator name)
                (getf (cddr source) :identity-with-one-argument)
                order)))))

(defun open-method-combination (build generic)
  (let ((specification (source-method-combination build generic)))
    (if (eq (first specification) 'standard) specification
        (destructuring-bind (kind qualifier operator identity order) specification
          (list kind qualifier (if (source-function-p build operator) (open-name build operator) operator)
                identity order)))))

(defun capture-method-composition (form)
  ;; The short producer also runs during ordinary open-stage initialization.
  ;; Only an explicit oracle query may retain its disposable method objects.
  (unless (eq *composition-source* :inactive)
    (setf *composition-source* (list form)))
  form)

(defun normalize-effective-source (form)
  "Expand composition macros while CALL-METHOD still has its original syntax."
  (labels ((method-form (method environment)
             (if (and (consp method) (eq (first method) 'make-method))
                 `(make-method ,(walk (second method) environment)) method))
           (walk (expression environment)
             (walk-source-form
              expression environment
              (lambda (node context lexical)
                (if (and (eq context :eval) (consp node) (eq (first node) 'call-method))
                    (values `(call-method ,(method-form (second node) lexical)
                               ,@(when (cddr node)
                                   (list (mapcar (lambda (method) (method-form method lexical)) (third node))))) t)
                    node)))))
    (walk form nil)))

(defun wrap-around-methods (around form)
  (if around `(call-method ,(first around) (,@(rest around) (make-method ,form))) form))

(defun prepare-open-generics (build)
  ;; Create accessor generics through the compatibility layer too. On some
  ;; hosts the native accessor GF lacks class-only MOP applicability queries.
  (dolist (name (build-generics build))
    (let* ((declaration (find-source-definition build 'defgeneric name))
           (method (find name (build-method-sources build) :key #'second :test #'equal))
           (lambda-list
             (cond (declaration (third declaration))
                   (method
                    (multiple-value-bind (qualifiers lambda-list body) (method-parts method)
                      (declare (ignore qualifiers body))
                      (let ((shape (method-lambda-shape (ordinary-method-lambda-list lambda-list))))
                        (append (lambda-shape-required shape)
                                (when (lambda-shape-optional shape)
                                  (cons '&optional (loop repeat (length (lambda-shape-optional shape)) collect (gensym "OPTIONAL"))))
                                (when (lambda-shape-rest shape) (list '&rest (lambda-shape-rest shape)))
                                (when (lambda-shape-keyp shape) '(&key &allow-other-keys))))))
                   ((consp name) '(value object))
                   (t '(object)))))
      (closer-mop:ensure-generic-function
       (open-name build name) :lambda-list lambda-list
       :generic-function-class (find-class 'closer-mop:standard-generic-function)
       :method-class (find-class 'closer-mop:standard-method)))))

(closer-mop:define-method-combination source-standard ()
  ((around (:around)) (before (:before)) (primary () :required t) (after (:after)))
  (let ((body `(multiple-value-prog1
                  (progn ,@(loop for method in before collect `(call-method ,method))
                    (call-method ,(first primary) ,(rest primary)))
                ,@(loop for method in (reverse after) collect `(call-method ,method)))))
    (capture-method-composition (wrap-around-methods around body))))

(closer-mop:define-method-combination source-short
    (qualifier operator identity &optional (order :most-specific-first))
  ((around (:around)) (primary * :order order :required t))
  ;; A single shared source producer avoids registering disposable combination
  ;; types in a host-global registry. Authored qualifiers retain their identity.
  (dolist (method primary)
    (unless (equal (method-qualifiers method) (list qualifier))
      (invalid-method-error method "Expected qualifier ~S." qualifier)))
  (capture-method-composition
   (wrap-around-methods
    around
    (if (and identity (null (rest primary))) `(call-method ,(first primary))
        `(,operator ,@(mapcar (lambda (method) `(call-method ,method)) primary))))))

(defun effective-method-source (build generic gf methods)
  ;; Native accessors need not use the compatibility layer's GF class. A
  ;; disposable composition generic accepts their MOP-ordered method objects;
  ;; none of its methods or resulting compiled functions are invoked.
  (let* ((name (gensym "COMPOSITION"))
         (oracle (closer-mop:ensure-generic-function
                  name :generic-function-class (find-class 'closer-mop:standard-generic-function)
                  :lambda-list (closer-mop:generic-function-lambda-list gf)
                  :argument-precedence-order (closer-mop:generic-function-argument-precedence-order gf)))
         (specification (source-method-combination build generic))
         (*composition-source* nil))
    (unwind-protect
         (progn
           (closer-mop:compute-effective-method
            oracle (if (eq (first specification) 'standard)
                       (closer-mop:find-method-combination oracle 'source-standard nil)
                       (closer-mop:find-method-combination oracle (first specification) (rest specification)))
            methods)
           (unless *composition-source*
             (unsupported :method-composition "The MOP did not invoke the source method combination."))
           (values-list *composition-source*))
      (fmakunbound name))))
