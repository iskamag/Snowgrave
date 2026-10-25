(in-package #:snowgrave)

;;; Facts describe declared types and sealed identities; mutable fields are never sampled.

(defstruct fact (type t) value known callable owned-callable)

(defstruct specialization name fact source)

(defstruct local-source name definition environment scope)

(defstruct local-scope (definitions nil) (cache (make-hash-table :test #'equal)))

(defun literal-fact (value)
  (make-fact :type (cond ((null value) 'null) ((eq value t) '(eql t))
                         ((numberp value) (type-of value))
                         (t (class-name (class-of value))))
             :value value :known t
             :callable (and (functionp value) value)
             :owned-callable (functionp value)))

(defun fact-function-designator (fact)
  (or (fact-callable fact)
      (and (fact-known fact) (symbolp (fact-value fact)) (fact-value fact))))

(defun fact-key (fact)
  (list (fact-type fact) (fact-known fact)
        (when (fact-known fact)
          (let ((value (fact-value fact)))
            (if (or (symbolp value) (numberp value) (characterp value)) value
                (or (gethash value (configuration-identities *configuration*))
                    (setf (gethash value (configuration-identities *configuration*)) (gensym "IDENTITY"))))))
        (fact-callable fact) (fact-owned-callable fact)))

(defun fact-union (left right)
  (if (equal (fact-key left) (fact-key right)) left
      (make-fact :type (if (equal (fact-type left) (fact-type right)) (fact-type left)
                          `(or ,(fact-type left) ,(fact-type right)))
                 :owned-callable (or (fact-owned-callable left) (fact-owned-callable right)))))

(defun configuration-data (configuration key)
  (getf (closed-unit-compiler-data (configuration-unit configuration)) key))

(defun configuration-plan (configuration key name)
  (find name (configuration-data configuration key) :key (lambda (plan) (getf plan :name)) :test #'equal))

(defun audit-callable-transfer (configuration fact destination)
  ;; Losing a value/type fact must not hide a reference to an unspecialized
  ;; function. Refuse these transfers instead of inferring mutable bindings.
  (let ((callee (fact-callable fact)))
    (when (or (fact-owned-callable fact)
              (and callee
                   (or (not (function-name-p callee))
                       (gethash callee (configuration-functions configuration))
                       (find callee (configuration-data configuration :layouts)
                             :key (lambda (layout) (getf layout :allocator))))))
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
          (configuration-data configuration :special-variables)))

(defun source-return-p (name form)
  (and (consp form) (not (eq (first form) 'quote))
       (or (and (eq (first form) 'return-from) (eq (second form) name))
           (some (lambda (part) (source-return-p name part)) form))))
