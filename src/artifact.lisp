(in-package #:snowgrave)

;;; Audit and serialize ordinary source for an independent Lisp process.

(defun check-residual-source (build forms)
  "The final source must contain no builder symbols or live builder objects."
  (let ((seen (make-hash-table :test #'eq)))
    (labels ((visit (value)
               (cond ((symbolp value)
                      (when (eq (symbol-package value) (build-open-package build))
                        (unsupported :builder-reference "Builder symbol remains: ~S." value)))
                     ((consp value)
                      (unless (gethash value seen)
                        (setf (gethash value seen) t) (visit (car value)) (visit (cdr value))))
                     ((or (numberp value) (characterp value) (stringp value)) nil)
                     ((simple-vector-p value) (map nil #'visit value))
                     (t (unsupported :builder-object "Non-source object remains: ~S." (type-of value))))))
      (visit forms))))

(defun package-bootstrap-forms (forms &optional required-packages)
  (let ((packages (make-hash-table :test #'equal)) (seen (make-hash-table :test #'eq)))
    (dolist (name required-packages) (setf (gethash name packages) nil))
    (labels ((visit (value)
               (cond ((symbolp value)
                      (let ((package (symbol-package value)))
                        (when (and package (not (member (package-name package) '("COMMON-LISP" "KEYWORD") :test #'string=)))
                          (pushnew (symbol-name value) (gethash (package-name package) packages) :test #'string=))))
                     ((consp value)
                      (unless (gethash value seen)
                        (setf (gethash value seen) t) (visit (car value)) (visit (cdr value))))
                     ((simple-vector-p value) (map nil #'visit value)))))
      (visit forms))
    (let ((package-variable (gensym "PACKAGE")) (name-variable (gensym "NAME")))
     (loop for name in (sort (loop for name being the hash-keys of packages collect name) #'string<)
          collect
            ;; Exporting referenced names in newly created source packages also
            ;; makes original single-colon literal symbols readable on replay.
          `(eval-when (:compile-toplevel :load-toplevel :execute)
              (unless (find-package ,name)
                (let ((,package-variable (make-package ,name :use '("COMMON-LISP"))))
                  (dolist (,name-variable ',(sort (gethash name packages) #'string<))
                    (shadow ,name-variable ,package-variable)
                    (export (intern ,name-variable ,package-variable) ,package-variable)))))))))

(defun write-unit-source (unit stream)
  ;; PRINT-READABLY may select host reader extensions for specialized strings.
  ;; The source domain is already checked; standard escaped syntax is portable.
  (let ((source-package (find-package (unit-plan-package (closed-unit-plan unit))))
        (*package* (find-package :cl)) (*print-readably* nil) (*print-escape* t)
        (*print-array* t) (*print-circle* t) (*print-pretty* t)
        (*print-level* nil) (*print-length* nil) (*print-base* 10))
    (write '(in-package #:common-lisp) :stream stream)
    (terpri stream)
    (dolist (form (package-bootstrap-forms (closed-unit-source unit) (list (package-name source-package))))
      (write form :stream stream) (terpri stream))
    ;; DEFSTRUCT may intern implementation-generated helper names in the
    ;; current package even when explicit constructor/accessor names are given.
    ;; Keep those names owned, and match the printer to the reader's package so
    ;; shadowed COMMON-LISP symbols retain their required qualification.
    (write `(in-package ,(package-name source-package)) :stream stream)
    (terpri stream)
    (let ((*package* source-package))
      (dolist (form (closed-unit-source unit))
        (write form :stream stream) (terpri stream)))))

(defun write-unit-metadata (unit stream)
  (let ((*package* (find-package :cl)) (*print-readably* nil) (*print-escape* t) (*print-array* t) (*print-circle* t)
        (*print-level* nil) (*print-length* nil) (*print-base* 10))
    (write (closed-unit-metadata unit) :stream stream) (terpri stream)))
