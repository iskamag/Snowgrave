(in-package #:snowgrave)

;;; The MOP may compile its effective method before returning it. Capture the
;;; source at the standard DEFINE-METHOD-COMBINATION boundary instead of
;;; inspecting a host-specific effective-method function or compiler closure.
(defvar *composition-source*)

(defun prepare-open-generics (build)
  ;; Create accessor generics through the compatibility layer too. On some
  ;; hosts the native accessor GF lacks class-only MOP applicability queries.
  (dolist (name (build-generics build))
    (let* ((declaration (find-if (lambda (form) (and (eq (first form) 'defgeneric)
                                                     (equal (second form) name))) (build-forms build)))
           (method (find name (build-method-sources build) :key #'second :test #'equal))
           (lambda-list
             (cond (declaration (third declaration))
                   (method
                    (multiple-value-bind (qualifiers lambda-list body) (method-parts method)
                      (declare (ignore qualifiers body))
                      (let ((shape (method-lambda-shape (ordinary-method-lambda-list lambda-list))))
                        (append (getf shape :required)
                                (when (getf shape :optional)
                                  (cons '&optional (loop repeat (length (getf shape :optional)) collect (gensym "OPTIONAL"))))
                                (when (getf shape :rest) (list '&rest (getf shape :rest)))
                                (when (getf shape :keyp) '(&key &allow-other-keys))))))
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
    (setf *composition-source*
          (if around `(call-method ,(first around) (,@(rest around) (make-method ,body))) body))))

(defun effective-method-source (gf methods)
  ;; Native accessors need not use the compatibility layer's GF class. A
  ;; disposable composition generic accepts their MOP-ordered method objects;
  ;; none of its methods or resulting compiled functions are invoked.
  (let* ((name (gensym "COMPOSITION"))
         (oracle (closer-mop:ensure-generic-function
                  name :generic-function-class (find-class 'closer-mop:standard-generic-function)
                  :lambda-list (closer-mop:generic-function-lambda-list gf)
                  :argument-precedence-order (closer-mop:generic-function-argument-precedence-order gf)))
         (*composition-source* nil))
    (unwind-protect
         (progn
           (closer-mop:compute-effective-method
            oracle (closer-mop:find-method-combination oracle 'source-standard nil) methods)
           (or *composition-source*
               (unsupported :method-composition "The MOP did not invoke the source method combination.")))
      (fmakunbound name))))
