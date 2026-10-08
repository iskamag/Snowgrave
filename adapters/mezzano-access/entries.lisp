;;;; Cold entry/call lowering for the caller-owned Mezzano register ABI.
(in-package #:snowgrave.mezzano-access)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun finite-entry-list-p (value)
    (handler-case (not (null (list-length value))) (type-error () nil)))

  (defun admitted-entry-plan (name arguments)
    "Parse the bounded required/optional ABI before emitting any entry.
Return receivers, sequential original bindings, minimum count and maximum count."
    (unless (and (finite-entry-list-p arguments)
                 (or (and (symbolp name) name)
                     (and (consp name) (eq (first name) 'setf)
                          (finite-entry-list-p name) (= (length name) 2)
                          (symbolp (second name)) (second name))))
      (error "Unsupported admitted entry name/lambda list."))
    (let ((optionalp nil) (required-count 0) (optional-count 0)
          (receivers nil) (bindings nil) (variables nil))
      (labels ((variable (value)
                 (unless (and (symbolp value) value (not (eq value t))
                              (not (keywordp value)) (not (member value lambda-list-keywords))
                              #+mezzano
                              (not (member (mezzano.internals::variable-information value) '(:special :constant)))
                              (not (member value variables)))
                   (error "Unsupported, special, constant or duplicate admitted entry variable."))
                 (push value variables)))
        (dolist (argument arguments)
          (cond ((eq argument '&optional)
                 (when optionalp (error "Duplicate &OPTIONAL in admitted entry ~S" name))
                 (setf optionalp t))
                ((member argument lambda-list-keywords)
                 (error "Unsupported admitted entry lambda list: ~S" arguments))
                (optionalp
                 (let* ((spec (if (consp argument) argument (list argument)))
                        (receiver (gensym "OPTIONAL")) (present (gensym "PRESENT")))
                   (unless (and (finite-entry-list-p spec) (<= 1 (length spec) 3))
                     (error "Unsupported admitted optional argument."))
                   (variable (first spec))
                   (when (= (length spec) 3) (variable (third spec)))
                   (push `(,receiver nil ,present) receivers)
                   (push `(,(first spec) (if ,present ,receiver ,(second spec))) bindings)
                   (when (third spec) (push `(,(third spec) ,present) bindings))
                   (incf optional-count)))
                (t
                 (variable argument)
                 (let ((receiver (gensym "REQUIRED")))
                   (push receiver receivers) (push `(,argument ,receiver) bindings))
                 (incf required-count)))))
      ;; Further optional receivers touch the caller stack in the native
      ;; prologue before the count guard. They need a separately admitted ABI.
      (when (> (+ required-count optional-count) 5)
        (error "Admitted entry exceeds the native register-argument profile: ~S" name))
      (values (nreverse receivers) (nreverse bindings)
              required-count (+ required-count optional-count))))

  (defun admitted-entry-expression (name arguments failure-form body block-name)
    "Emit one checked receiver/count/default/body contract for named or anonymous entries.
Return the lowered lambda list, function body prefix and one executable expression."
    (let ((documentation nil) (declarations nil))
      (when (stringp (first body)) (setf documentation (pop body)))
      (loop while (and (consp (first body)) (eq (caar body) 'declare))
            do (push (pop body) declarations))
      #+mezzano
      (multiple-value-bind (receivers bindings minimum maximum)
          (admitted-entry-plan name arguments)
        (when (some (lambda (declaration) (assoc 'special (cdr declaration))) declarations)
          (error "Admitted entry requires lexical parameters: ~S" name))
        (let ((ignored-rest (gensym "UNUSED-REST")) (count (gensym "ARGUMENT-COUNT")))
          (values `(&optional ,@receivers &rest ,ignored-rest mezzano.internals::&count ,count)
                  (append (when documentation (list documentation)) (list `(declare (ignore ,ignored-rest))))
                  ;; The generated count predicate is part of this entry too.
                  ;; An enclosing access marker must not redirect its failure
                  ;; to a caller block, introducing a nonlocal closure capture.
                  `(with-admitted-access (return-from ,block-name ,failure-form)
                     (if (or ,@(loop for accepted from minimum to maximum collect `(eql ,count ,accepted)))
                         (let* ,bindings ,@(nreverse declarations) ,@body)
                         ,failure-form)))))
      #-mezzano
      (values arguments (append (when documentation (list documentation)) (nreverse declarations))
              `(with-admitted-access (return-from ,block-name ,failure-form) ,@body))))

  (defmacro define-admitted-entry (name arguments failure-form &body body)
    "Define an owner entry with bounded bad-count and access failure returns.
On Mezzano accept at most five required/optional positional arguments. Check
the actual count before defaults, original parameter declarations or body.
FAILURE-FORM must be usable before parameter bindings exist. Code/data/stack
residence, callable arity, captures, global cells and lifetime remain owner proofs.
Outside Mezzano retain ordinary DEFUN lambda-list and error behavior."
    (multiple-value-bind (lambda-list prefix expression)
        (admitted-entry-expression name arguments failure-form body (if (consp name) (second name) name))
      `(defun ,name ,lambda-list ,@prefix ,expression)))

  (defmacro admitted-lambda (arguments failure-form &body body)
    "Return FUNCTION of an anonymous entry using the shared bounded entry ABI.
The same required/optional max-five count check precedes defaults and body on
Mezzano. A fresh private block handles access rejection without capturing a
caller RETURN/RETURN-FROM. FAILURE-FORM may use its existing outer lexical
blocks but cannot depend on original parameters before the count guard.
Ordinary host lambda-list errors remain ordinary. Closure construction, capture
and callback/stack/lifetime admission are separate owner obligations."
    (let ((block-name (gensym "ANONYMOUS-ENTRY")))
      (multiple-value-bind (lambda-list prefix expression)
          (admitted-entry-expression block-name arguments failure-form body block-name)
        `(function (lambda ,lambda-list ,@prefix (block ,block-name ,expression))))))

  (defmacro call-admitted-entry (function &rest arguments &environment environment)
    "Call an admitted native function/closure after a bounded callable-tag check.
Evaluate FUNCTION then arguments once in ordinary left-to-right order. The
lexical scope supplies the exact failure; outside it retain ordinary FUNCALL.
The tag test grants no code, count, capture, residence or lifetime admission."
    #+mezzano
    (multiple-value-bind (failure admittedp) (admitted-access-failure environment)
      (if (not admittedp) `(funcall ,function ,@arguments)
          (progn
            (unless (and (finite-entry-list-p arguments) (<= (length arguments) 5))
              (error "Admitted call exceeds the native register-argument profile."))
            (let ((entry (gensym "ENTRY"))
                  (values (loop for argument in arguments collect (gensym "ARGUMENT"))))
              `(let ((,entry ,function)
                     ,@(loop for value in values for argument in arguments collect `(,value ,argument)))
                 (if (or (mezzano.internals::%object-of-type-p ,entry mezzano.internals::+object-tag-function+)
                         (mezzano.internals::%object-of-type-p ,entry mezzano.internals::+object-tag-closure+))
                     (mezzano.runtime::%funcall ,entry ,@values)
                     ,failure))))))
    #-mezzano
    (declare (ignore environment))
    #-mezzano `(funcall ,function ,@arguments)))
