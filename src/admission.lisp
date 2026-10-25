(in-package #:snowgrave)

;;; Source admission and binding resolution. These functions select names or
;;; reject unsupported operations; they do not rebuild expressions or emit code.

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

;; These are argument positions, not inferred values. A literal symbol in a
;; standard callback position denotes a global function, even inside FLET.
(defparameter *callback-arguments*
  '((funcall 0) (apply 0) (multiple-value-call 0)
    (mapcar 0) (mapc 0) (mapcan 0) (maplist 0) (mapl 0) (mapcon 0)
    (map 1) (map-into 1) (maphash 0)
    (every 0) (some 0) (notevery 0) (notany 0) (complement 0)
    (reduce 0) (sort 1) (stable-sort 1) (merge 3)
    (find-if 0) (find-if-not 0) (position-if 0) (position-if-not 0)
    (count-if 0) (count-if-not 0) (remove-if 0) (remove-if-not 0)
    (delete-if 0) (delete-if-not 0)
    (substitute-if 1) (substitute-if-not 1)
    (nsubstitute-if 1) (nsubstitute-if-not 1)
    (member-if 0) (member-if-not 0) (assoc-if 0) (assoc-if-not 0)
    (rassoc-if 0) (rassoc-if-not 0)
    (subst-if 1) (subst-if-not 1) (nsubst-if 1) (nsubst-if-not 1)))

;; The value is the first keyword argument position for the standard operator.
(defparameter *callback-keywords*
  '((find . 2) (find-if . 2) (find-if-not . 2)
    (position . 2) (position-if . 2) (position-if-not . 2)
    (count . 2) (count-if . 2) (count-if-not . 2)
    (remove . 2) (remove-if . 2) (remove-if-not . 2)
    (delete . 2) (delete-if . 2) (delete-if-not . 2)
    (substitute . 3) (substitute-if . 3) (substitute-if-not . 3)
    (nsubstitute . 3) (nsubstitute-if . 3) (nsubstitute-if-not . 3)
    (remove-duplicates . 1) (delete-duplicates . 1)
    (reduce . 2) (sort . 2) (stable-sort . 2) (merge . 4)
    (search . 2) (mismatch . 2)
    (member . 2) (member-if . 2) (member-if-not . 2)
    (assoc . 2) (assoc-if . 2) (assoc-if-not . 2)
    (rassoc . 2) (rassoc-if . 2) (rassoc-if-not . 2)
    (adjoin . 2) (union . 2) (nunion . 2)
    (intersection . 2) (nintersection . 2) (subsetp . 2)
    (set-difference . 2) (nset-difference . 2)
    (set-exclusive-or . 2) (nset-exclusive-or . 2)
    (tree-equal . 2) (subst . 3) (nsubst . 3)
    (subst-if . 3) (subst-if-not . 3) (nsubst-if . 3) (nsubst-if-not . 3)))

(defun allowed-function-p (build name phase)
  (let ((symbol (if (consp name) (second name) name)))
    (or (source-function-p build name)
        (member name (getf (build-declaration build) :external-operations) :test #'equal)
        (and (symbolp symbol)
             (or (eq (symbol-package symbol) (find-package :cl))
                 (eq (symbol-package symbol) (build-output-package build))
                 (and (eq phase :open)
                      (eq (symbol-package symbol) (build-open-package build))))))))

(defun require-owned-class-universe (build)
  (unless (build-classes build)
    (unsupported :external-construction "MAKE-INSTANCE needs an owned class universe.")))

(defun representation-sensitive-type-p (type)
  (cond ((member type '(structure-object standard-object generic-function compiled-function)) t)
        ;; Logical metadata are ordinary structures, not host metaobjects.
        ;; Refuse these physical assertions until logical TYPEP is provided.
        ((and (symbolp type) (find-class type nil)
              (subtypep type 'closer-mop:metaobject)) t)
        ((consp type) (some #'representation-sensitive-type-p type))))

(defun check-source-type (type phase)
  (when (and (eq phase :closed) (representation-sensitive-type-p type))
    (unsupported :physical-type "Physical type ~S needs a logical representation check." type)))

(defun check-source-operation (build name phase &key referencep)
  ;; Logical operations have an explicit closed binding. Everything else uses
  ;; the same policy for direct calls and function references, with the latter
  ;; also refusing record operations that require an explicit source operand.
  (unless (or (eq phase :open)
              (metadata-operation-name name)
              (eq name 'make-instance)
              (observation-function-name build name phase))
    (let ((feature
            (cond ((and referencep (member name *indirect-record-operations* :test #'equal))
                   :indirect-open-operation)
                  ((member name *unsupported-operations*)
                   (if referencep :indirect-open-operation :open-operation))
                  ((and (build-classes build) (member name *representation-observers*))
                   (if referencep :indirect-open-operation :representation-observation)))))
      (when feature
        (unsupported feature "Operation ~S has no closed ~A realization."
                     name (if referencep "function-reference" "source"))))))

(defun resolve-ordinary-function (build name phase environment)
  (cond ((source-local-function-p name environment) name)
        ((source-function-p build name) (mapped-name build name phase))
        ((allowed-function-p build name phase) name)
        (t (error 'unclosed-call :feature :external-call
                  :detail (format nil "Function ~S is neither source-owned nor declared external." name)))))

(defun resolve-function-reference (build name phase environment)
  (when (source-local-function-p name environment)
    (return-from resolve-function-reference name))
  (check-source-operation build name phase :referencep t)
  (cond ((eq name 'make-instance)
         (require-owned-class-universe build)
         (record-make-instance-name build phase))
        ((metadata-operation-name name) (metadata-function-name build name phase))
        ((observation-function-name build name phase))
        (t (resolve-ordinary-function build name phase environment))))
