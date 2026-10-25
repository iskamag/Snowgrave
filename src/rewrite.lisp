(in-package #:snowgrave)

;;; Rebuild owned source using the admitted bindings. Lexical traversal stays
;;; in WALK-SOURCE-FORM; policy and name resolution stay in admission.lisp.

(defun rewrite-callback-designators (form resolve)
  (let ((arguments (copy-list (rest form))) (changed nil))
    (labels ((replace-at (position)
               (let ((argument (nth position arguments)))
                 (when (and (quoted argument) (second argument)
                            (symbolp (second argument)))
                   (let ((name (funcall resolve (second argument) nil)))
                     ;; Keep symbol lookup global and at invocation time.
                     ;; FUNCTION here would capture a same-named FLET binding.
                     (unless (eq name (second argument))
                       (setf (nth position arguments) (list 'quote name)
                             changed t)))))))
      (dolist (position (rest (assoc (first form) *callback-arguments*)))
        (replace-at position))
      (let ((start (cdr (assoc (first form) *callback-keywords*))))
        (when start
          (loop for position from start below (1- (length arguments)) by 2
                when (member (nth position arguments) '(:key :test :test-not))
                  do (replace-at (1+ position))))))
    (if changed (cons (first form) arguments) form)))

(defun rewrite-variable-name (build name phase)
  (if (member name (build-globals build)) (mapped-name build name phase) name))

(defun rewrite-lambda-bindings (build lambda-list phase)
  (let ((mode :required))
    (mapcar
     (lambda (item)
       (cond ((member item lambda-list-keywords) (setf mode item) item)
             ((symbolp item)
              (let ((mapped (rewrite-variable-name build item phase)))
                (if (and (eq mode '&key) (not (eq item mapped)))
                    (list (list (intern (symbol-name item) :keyword) mapped))
                    mapped)))
             ((member mode '(&optional &aux))
              (list* (rewrite-variable-name build (first item) phase)
                     (second item)
                     (when (cddr item) (list (rewrite-variable-name build (third item) phase)))))
             ((eq mode '&key)
              (list* (if (consp (first item))
                         (list (first (first item)) (rewrite-variable-name build (second (first item)) phase))
                         (let* ((variable (first item)) (mapped (rewrite-variable-name build variable phase)))
                           (if (eq mapped variable) variable
                               (list (intern (symbol-name variable) :keyword) mapped))))
                     (second item)
                     (when (cddr item) (list (rewrite-variable-name build (third item) phase)))))
             (t item)))
     lambda-list)))

(defun rewrite-body-declarations (build body phase)
  (mapcar
   (lambda (form)
     (if (and (consp form) (eq (first form) 'declare))
         (cons 'declare
               (mapcar (lambda (spec)
                         (case (first spec)
                           ((special ignore ignorable dynamic-extent)
                            (cons (first spec) (mapcar (lambda (name) (rewrite-variable-name build name phase)) (rest spec))))
                           (type (list* 'type (rewrite-type build (second spec) phase)
                                        (mapcar (lambda (name) (rewrite-variable-name build name phase)) (cddr spec))))
                           (otherwise spec)))
                       (remove nil (mapcar (lambda (spec) (normalize-host-declaration (first spec) spec))
                                           (rest form)))))
         form))
   body))

(defun rewrite-type (build type phase)
  (check-source-type type phase)
  (cond ((source-class-p build type)
         (if (eq phase :open) (open-name build type)
             ;; DECLARE/THE class assertions are not logical TYPEP operations.
             ;; A union of the actual structures implements the class domain.
             (cons 'or (loop for description in (build-layouts build)
                            when (member type (class-description-cpl description))
                              collect (class-description-type description)))))
        ((consp type) (cons (first type) (mapcar (lambda (x) (rewrite-type build x phase)) (rest type))))
        (t type)))

(defun rewrite-binding-form (build node phase)
  (case (first node)
    (lambda
     (list* 'lambda (rewrite-lambda-bindings build (second node) phase)
            (rewrite-body-declarations build (cddr node) phase)))
    ((let let*)
     (list* (first node)
            (mapcar (lambda (binding)
                      (if (symbolp binding) (rewrite-variable-name build binding phase)
                          (cons (rewrite-variable-name build (first binding) phase) (rest binding))))
                    (second node))
            (rewrite-body-declarations build (cddr node) phase)))
    ((flet labels)
     (list* (first node)
            (mapcar (lambda (definition)
                      (list* (first definition)
                             (rewrite-lambda-bindings build (second definition) phase)
                             (rewrite-body-declarations build (cddr definition) phase)))
                    (second node))
            (rewrite-body-declarations build (cddr node) phase)))
    (locally
     (cons 'locally (rewrite-body-declarations build (rest node) phase)))))

(defun rewrite-form (build form phase &key environment)
  (labels
      ((call (name arguments lexical)
         (cons name (mapcar (lambda (part) (walk part lexical)) arguments)))
       (replacement (original new lexical)
         (if (eq (first original) (first new))
             (call (first new) (rest new) lexical)
             (walk new lexical)))
       (walk (expression env)
         (walk-source-form
          expression env
          (lambda (node context lexical)
            (when (and (eq context :eval) (consp node)
                       (not (source-local-function-p (first node) lexical)))
              (check-source-operation build (first node) phase))
            (cond
              ((and (eq context :set) (symbolp node)) (rewrite-variable-name build node phase))
              ((not (eq context :eval)) node)
              ((symbolp node)
               (if (and (member node (build-globals build))
                        (not (source-lexical-variable-p node lexical)))
                   (if (member node (build-constants build))
                       ;; Generated methods/constructors can be compiled
                       ;; before the source constant is initialized. An
                       ;; explicit cell read preserves initialization order
                       ;; without falsely declaring the constant SPECIAL.
                       (values (list 'symbol-value (list 'quote (mapped-name build node phase))) t)
                       (mapped-name build node phase))
                   node))
              ((or (stringp node) (simple-vector-p node))
               (values (literal-reference build node phase) t))
              ((atom node) node)
              ((eq (first node) 'quote)
               (let ((value (second node)))
                 (values (if (or (consp value) (arrayp value))
                             (literal-reference build value phase) node) t)))
              ((eq (first node) 'function)
               (let ((target (second node)))
                 (if (function-name-p target)
                     (values (list 'function (resolve-function-reference build target phase lexical)) t)
                     node)))
              ((member (first node) '(lambda let let* flet labels locally))
               (let ((replacement (rewrite-binding-form build node phase)))
                 (if (equal replacement node) node replacement)))
              ((and (symbolp (first node)) (source-local-function-p (first node) lexical)) node)
              ((or (assoc (first node) *callback-arguments*)
                   (assoc (first node) *callback-keywords*))
               (let ((replacement (rewrite-callback-designators
                                   node (lambda (name environment)
                                          (resolve-function-reference build name phase environment)))))
                 (if (eq replacement node) node
                     (values (walk replacement lexical) t))))
              ((metadata-operation-name (first node))
               (multiple-value-bind (replacement handled)
                   (metadata-operation-form build node phase)
                 (if handled (values (replacement node replacement lexical) t) node)))
              ((and (eq phase :closed) (build-classes build) (eq (first node) 'equalp))
               (values (call (observation-function-name build 'equalp phase) (rest node) lexical) t))
              ((eq (first node) 'the)
               (values (list 'the (rewrite-type build (second node) phase)
                             (walk (third node) lexical)) t))

              ((and (eq (first node) 'setf)
                    (loop for (place value) on (rest node) by #'cddr
                          thereis (and (consp place) (eq (first place) 'slot-value))))
               ;; Handle the standard place before a host SETF expander can
               ;; turn it into a private CLOS primitive. Evaluate its operands
               ;; exactly once, in the standard place-then-value order.
               (values
                (walk `(progn
                         ,@(loop for (place value) on (rest node) by #'cddr
                                 collect
                                 (if (and (consp place) (eq (first place) 'slot-value))
                                     (let* ((object (gensym "OBJECT")) (slot (gensym "SLOT"))
                                            (new (gensym "VALUE"))
                                            (reader (record-operation-form build place phase)))
                                       `(let* ((,object ,(second place)) (,slot ,(third place)) (,new ,value))
                                          (funcall #'(setf ,(first reader)) ,new ,object
                                                   ,@(when (cddr reader) (list slot)))))
                                     `(setf ,place ,value)))) lexical) t))
              ((member (first node) '(make-instance slot-value slot-boundp slot-makunbound typep))
               (when (and (eq (first node) 'typep) (quoted (third node)))
                 (check-source-type (second (third node)) phase))
               (multiple-value-bind (replacement handled)
                   (record-operation-form build node phase)
                 (if handled (values (replacement node replacement lexical) t) node)))
              ((and (symbolp (first node))
                    (or (source-function-p build (first node))
                        (and (not (special-operator-p (first node)))
                             (not (cl-environments:macro-function (first node) lexical)))))
               (let ((name (resolve-ordinary-function build (first node) phase lexical)))
                 (if (eq name (first node)) node
                     (values (call name (rest node) lexical) t))))
              (t node))))))
    (walk form environment)))

(defun ordinary-method-lambda-list (lambda-list)
  (let ((requiredp t))
    (mapcar (lambda (item)
              (when (member item lambda-list-keywords) (setf requiredp nil))
              (if (and requiredp (consp item)) (first item) item))
            lambda-list)))
