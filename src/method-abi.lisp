(in-package #:snowgrave)

;;; Bounded calls carry scalars; variable tails retain the ordinary list convention.

(defstruct method-call-abi arguments required optional-count list-parameter)

(defun make-generic-call-abi (shape)
  (if (or (lambda-shape-rest shape) (lambda-shape-keyp shape))
      (make-method-call-abi :list-parameter (gensym "ARGUMENTS"))
      (make-method-call-abi
       :required (length (lambda-shape-required shape))
       :arguments (loop repeat (+ (length (lambda-shape-required shape))
                                  (length (lambda-shape-optional shape))) collect (gensym "ARGUMENT"))
       :optional-count (when (lambda-shape-optional shape) (gensym "OPTIONAL-COUNT")))))

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

(defun call-abi-lambda (abi lambda-form &optional required-types)
  (cond ((method-call-abi-list-parameter abi)
         (let ((arguments (method-call-abi-list-parameter abi)))
           ;; Expose each incoming specializer to the compiler before method
           ;; defaults or assignments can change the source parameters.
           `(apply (function ,lambda-form)
                   ,@(loop for type in required-types for index from 0
                           collect `(the ,type (nth ,index ,arguments)))
                   ,(if required-types `(nthcdr ,(length required-types) ,arguments) arguments))))
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
