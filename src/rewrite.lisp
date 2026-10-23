(in-package #:snowgrave)

;;; This is a binding transformation over the host lexical walker. It does
;;; not infer values, call effects, or fields, and never emits scratch code.

(defparameter *unsupported-operations*
  '(eval compile compile-file load fdefinition symbol-function
    find-class class-of class-name change-class make-instances-obsolete
    update-instance-for-redefined-class update-instance-for-different-class
    ensure-generic-function add-method remove-method find-method
    compute-applicable-methods function-lambda-expression
    make-load-form progv))

(defparameter *indirect-record-operations*
  '(make-instance slot-value slot-boundp slot-makunbound typep
    (setf slot-value)))

(defparameter *representation-observers*
  '(equalp sxhash describe inspect print-object print prin1 princ write
    write-to-string prin1-to-string princ-to-string format))

(defun local-function-p (name environment)
  (nth-value 1 (sb-cltl2:function-information name environment)))

(defun allowed-function-p (build name phase)
  (let ((symbol (if (consp name) (second name) name)))
    (or (source-function-p build name)
        (member name (getf (build-declaration build) :external-operations) :test #'equal)
        (and (symbolp symbol)
             (or (eq (symbol-package symbol) (find-package :cl))
                 (eq (symbol-package symbol) (build-output-package build))
                 (and (eq phase :open) (eq (symbol-package symbol) (build-open-package build)))
                 ;; The host lexical walker expands standard control/binders
                 ;; into implementation primitives. PCL calls remain excluded.
                 (and (symbol-package symbol)
                      (member (package-name (symbol-package symbol))
                              '("SB-INT" "SB-KERNEL" "SB-C" "SB-IMPL" "SB-EXT")
                              :test #'string=)))))))


(defun representation-sensitive-type-p (type)
  (cond ((member type '(structure-object standard-object generic-function compiled-function)) t)
        ((consp type) (some #'representation-sensitive-type-p type))))

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
                       (rest form)))
         form))
   body))

(defun rewrite-type (build type phase)
  (when (and (eq phase :closed) (representation-sensitive-type-p type))
    (unsupported build :physical-type "Physical type ~S needs a logical representation check." type))
  (cond ((source-class-p build type)
         (if (eq phase :open) (open-name build type)
             ;; DECLARE/THE class assertions are not logical TYPEP operations.
             ;; A union of the actual structures implements the class domain.
             (cons 'or (loop for description in (build-layouts build)
                            when (member type (class-description-cpl description))
                              collect (class-description-type description)))))
        ((consp type) (cons (first type) (mapcar (lambda (x) (rewrite-type build x phase)) (rest type))))
        (t type)))

(defun rewrite-form (build form phase &key environment)
  (let ((sb-walker::*walk-form-expand-macros-p* t))
    (labels
        ((function-reference (name env)
           (cond ((local-function-p name env) name)
                 ((and (eq phase :closed)
                       (or (member name *indirect-record-operations* :test #'equal)
                           (member name *unsupported-operations*)))
                  (unsupported build :indirect-open-operation
                               "Function reference ~S needs an explicit closed operation." name))
                 ((source-function-p build name) (mapped-name build name phase))
                 ((allowed-function-p build name phase) name)
                 (t (error 'unclosed-call :feature :external-call
                           :detail (format nil "Function ~S is neither source-owned nor declared external." name)))))
         (walk (expression env)
           (sb-walker:walk-form
            expression env
            (lambda (node context lexical)
              (cond
                ((and (eq context :set) (symbolp node)) (rewrite-variable-name build node phase))
                ((not (eq context :eval)) node)
                ((symbolp node)
                 (if (and (member node (build-globals build))
                          (not (sb-walker:var-lexical-p node lexical)))
                     (mapped-name build node phase) node))
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
                       (values (list 'function (function-reference target lexical)) t)
                       node)))
                ((member (first node) '(lambda let let* flet labels locally))
                 (let ((replacement
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
                            (cons 'locally (rewrite-body-declarations build (rest node) phase))))))
                   (if (equal replacement node) node replacement)))
                ((and (symbolp (first node)) (local-function-p (first node) lexical)) node)
                ((and (member (first node) '(funcall apply multiple-value-call)) (quoted (second node))
                      (function-name-p (second (second node))))
                 (values (walk (list* (first node)
                                      (list 'function (function-reference (second (second node)) lexical))
                                      (cddr node)) lexical) t))
                ((and (eq phase :closed) (member (first node) *unsupported-operations*))
                 (unsupported build :open-operation "Operation ~S has no closed source realization." (first node)))
                ((and (eq phase :closed) (build-classes build)
                      (member (first node) *representation-observers*))
                 (unsupported build :representation-observation
                              "~S needs a logical record observation implementation." (first node)))
                ((eq (first node) 'the)
                 (values (list 'the (rewrite-type build (second node) phase)
                               (walk (third node) lexical)) t))
                ((and (eq (first node) 'typep) (eq phase :closed)
                      (quoted (third node))
                      (representation-sensitive-type-p (second (third node))))
                 (unsupported build :physical-type "Physical record types are not logical source types."))
                ((member (first node) '(make-instance slot-value slot-boundp slot-makunbound typep))
                 (multiple-value-bind (replacement handled)
                     (record-operation-form build node phase)
                   (if handled
                       ;; Walk operands, not the replacement's operator again:
                       ;; open MAKE-INSTANCE is still a host construction.
                       (values (if (eq phase :open)
                                   (cons (first replacement)
                                         (mapcar (lambda (part) (walk part lexical)) (rest replacement)))
                                   (walk replacement lexical)) t)
                       node)))
                ((eq (first node) 'sb-pcl::set-slot-value)
                 (if (eq phase :open) node
                     (let* ((reader (record-operation-form build
                                      (list 'slot-value (second node) (third node)) :closed))
                            (object (gensym "OBJECT")) (slot (gensym "SLOT")) (value (gensym "VALUE")))
                       (values
                        (walk (list 'let* (list (list object (second node)) (list slot (third node))
                                               (list value (fourth node)))
                                    (list 'funcall (list 'function (list 'setf (first reader)))
                                          value object slot))
                              lexical)
                        t))))
                ((and (symbolp (first node)) (source-function-p build (first node)))
                 (values (cons (mapped-name build (first node) phase)
                               (mapcar (lambda (part) (walk part lexical)) (rest node))) t))
                ((and (symbolp (first node))
                      (not (special-operator-p (first node)))
                      (not (macro-function (first node) lexical)))
                 (unless (allowed-function-p build (first node) phase)
                   (error 'unclosed-call :feature :external-call
                          :detail (format nil "Call to undeclared function ~S." (first node))))
                 node)
                (t node))))))
      (walk form environment))))

(defun ordinary-method-lambda-list (lambda-list)
  (let ((requiredp t))
    (mapcar (lambda (item)
              (when (member item lambda-list-keywords) (setf requiredp nil))
              (if (and requiredp (consp item)) (first item) item))
            lambda-list)))
