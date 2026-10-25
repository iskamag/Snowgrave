(in-package #:snowgrave)

(defun entry-domain-test (build domain variable)
  (cond ((source-class-p build domain) (closed-class-test build domain variable))
        ((and (consp domain) (eq (first domain) 'eql))
         (unless (or (numberp (second domain)) (characterp (second domain)) (symbolp (second domain)))
           (unsupported :configuration-input "Object identity capture is outside the source core."))
         `(eql ,variable ',(second domain)))
        (t `(typep ,variable ',domain))))

(defun emit-functions (build)
  (dolist (form (build-forms build))
    (when (eq (first form) 'defun)
      (destructuring-bind (operator name lambda-list &rest body) form
        (declare (ignore operator))
        (multiple-value-bind (prefix executable) (body-parts body)
          (let* ((entryp (member name (getf (build-declaration build) :entries) :test #'equal))
                 (domains (second (assoc name (getf (build-declaration build) :external-domains) :test #'equal)))
                 (checks
                   (when entryp
                     (unless (and (every #'symbolp lambda-list)
                                  (notany (lambda (x) (member x lambda-list-keywords)) lambda-list)
                                  (= (length lambda-list) (length domains)))
                       (unsupported :entry-domain
                                    "Entry ~S needs required parameters and one declared domain per parameter." name))
                     (loop for variable in lambda-list for domain in domains
                           collect `(unless ,(entry-domain-test build domain variable)
                                       (error 'type-error :datum ,variable :expected-type ',domain)))))
                 (lambda-form
                   (rewrite-form build
                                 `(lambda ,lambda-list ,@prefix
                                     (block ,(if (consp name) (second name) name)
                                       ,@checks ,@executable))
                                 :closed)))
            (emit-form build (list* 'defun (closed-name build name) (rest lambda-form)))))))
    ;; Keep source initialization order: constants must be established before
    ;; compiling their users, and their initializers may call earlier helpers.
    (when (member (first form) '(defvar defparameter defconstant))
      (emit-form build (list* (first form) (closed-name build (second form))
                             (when (cddr form)
                               (cons (rewrite-form build (third form) :closed) (cdddr form))))))))
