(in-package #:snowgrave)

;;; Facts describe declared types and sealed identities; mutable fields are never sampled.

;; Extending a contour pushes bindings onto its own slots; outer alists stay shared and unchanged.
(defstruct (lexical-facts (:conc-name env-)) variables functions)
(defstruct lambda-source form environment)

(defstruct fact (type t) value known callable (owned-callable nil :type boolean))

(defstruct specialization name fact source)

(defstruct local-source name definition environment scope)

(defstruct local-scope (definitions nil) (cache (make-hash-table :test #'equal)))

(defun configuration-plan (configuration)
  (closed-unit-plan (configuration-unit configuration)))

(defun literal-fact (value)
  (let ((callable (and (functionp value) value)))
    (make-fact :type (cond ((null value) 'null) ((eq value t) '(eql t))
                           ((numberp value) (type-of value))
                           (t (class-name (class-of value))))
               :value value :known t :callable callable
               :owned-callable (not (null callable)))))

(defun fact-function-designator (fact)
  (or (fact-callable fact)
      (and (fact-known fact) (symbolp (fact-value fact)) (fact-value fact))))

(defun fact-key (configuration fact)
  (let ((callable (fact-callable fact)))
    (list (fact-type fact) (fact-known fact)
          (when (fact-known fact)
            (let ((value (fact-value fact)))
              (if (or (symbolp value) (numberp value) (characterp value)) value
                  (or (gethash value (configuration-identities configuration))
                      (setf (gethash value (configuration-identities configuration)) (gensym "IDENTITY"))))))
          ;; Compare lambda syntax within the same contour. Do not descend into
          ;; lexical records: recursive LABELS scopes can contain cycles.
          (if (lambda-source-p callable)
              (list (lambda-source-form callable) (lambda-source-environment callable))
              callable)
          (fact-owned-callable fact))))

(defun fact-union (configuration left right)
  (if (equal (fact-key configuration left) (fact-key configuration right)) left
      (make-fact :type (if (equal (fact-type left) (fact-type right)) (fact-type left)
                          `(or ,(fact-type left) ,(fact-type right)))
                 :owned-callable (or (fact-owned-callable left) (fact-owned-callable right)))))

(defun audit-callable-transfer (configuration fact destination)
  ;; Lost type/value facts must not hide a reference to an unspecialized function.
  (let ((callee (fact-callable fact))
        (plan (configuration-plan configuration)))
    (when (or (fact-owned-callable fact)
              (and callee
                   (or (not (function-name-p callee))
                       (gethash callee (configuration-functions configuration))
                       (member callee (unit-plan-construction-functions plan) :test #'equal))))
      (unsupported :configuration-indirect-call
                   "Owned function value escapes through ~S." destination))))

(defun canonical-source (form)
  (walk-source-form form nil (lambda (node context environment)
                               (declare (ignore context environment)) node)))

(defun authored-load-time-value-p (form)
  (and (consp form) (not (eq (first form) 'quote))
       (or (eq (first form) 'load-time-value)
           (some #'authored-load-time-value-p form))))

(defun assigned-source-variables (form)
  ;; Over-approximating assignments is safe: a shadowed name can lose a fact,
  ;; but a mutable binding must never retain its incoming value/type promise.
  (let ((names nil))
    (walk-source-form form nil
      (lambda (node context environment)
        (declare (ignore environment))
        (when (and (eq context :set) (symbolp node)) (pushnew node names))
        node))
    names))

(defun declared-special-variables (body)
  (multiple-value-bind (prefix forms) (body-parts body)
    (declare (ignore forms))
    (loop for declaration in prefix when (consp declaration) append
      (loop for spec in (rest declaration) when (eq (first spec) 'special) append (rest spec)))))

(defun unstable-source-variables (configuration form body)
  (append (assigned-source-variables form) (declared-special-variables body)
          (unit-plan-special-variables (configuration-plan configuration))))

(defun source-return-p (name form)
  (and (consp form) (not (eq (first form) 'quote))
       (or (and (eq (first form) 'return-from) (eq (second form) name))
           (some (lambda (part) (source-return-p name part)) form))))
