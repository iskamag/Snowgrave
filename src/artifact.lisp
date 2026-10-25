(in-package #:snowgrave)

;;; Audit and serialize ordinary source for an independent Lisp process.

(defun visit-source-leaves (function forms)
  (let ((seen (make-hash-table :test #'eq)))
    (labels ((visit (value)
               (if (or (consp value) (simple-vector-p value))
                   (unless (gethash value seen)
                     (setf (gethash value seen) t)
                     (if (consp value)
                         (progn (visit (car value)) (visit (cdr value)))
                         (map nil #'visit value)))
                   (funcall function value))))
      (visit forms))))

(defun check-residual-source (build forms)
  "The final source must contain no builder symbols or live builder objects."
  (visit-source-leaves
   (lambda (value)
     (cond ((symbolp value)
            (when (eq (symbol-package value) (build-open-package build))
              (unsupported :builder-reference "Builder symbol remains: ~S." value)))
           ((or (numberp value) (characterp value) (stringp value)) nil)
           (t (unsupported :builder-object "Non-source object remains: ~S." (type-of value)))))
   forms))

(defun shadowed-names (names)
  "Referenced names a package using COMMON-LISP would otherwise inherit."
  (sort (remove-if-not (lambda (name)
                         (eq (nth-value 1 (find-symbol name :cl)) :external))
                       names)
        #'string<))

(defun package-bootstrap-forms (forms &optional required-packages)
  (let ((packages (make-hash-table :test #'equal)))
    (dolist (name required-packages) (setf (gethash name packages) nil))
    (visit-source-leaves
     (lambda (value)
       (when (symbolp value)
         (let ((package (symbol-package value)))
           (when (and package (not (member (package-name package) '("COMMON-LISP" "KEYWORD") :test #'string=)))
             (pushnew (symbol-name value) (gethash (package-name package) packages) :test #'string=)))))
     forms)
    (let* ((package-variable (gensym "PACKAGE")) (name-variable (gensym "NAME"))
           (entries (loop for name in (sort (loop for name being the hash-keys of packages collect name)
                                            #'string<)
                          collect (cons name (shadowed-names (gethash name packages))))))
      (when entries
        (list
         ;; One form rather than one per package. A freshly created package needs
         ;; its own symbols only for names COMMON-LISP would otherwise supply;
         ;; everything else interns on read. The writer never emits single-colon
         ;; references, so those symbols need no export.
         `(eval-when (:compile-toplevel :load-toplevel :execute)
            (dolist (,name-variable ',(mapcar #'car entries))
              (unless (find-package ,name-variable)
                (make-package ,name-variable :use '("COMMON-LISP"))))
            ,@(loop for (name . conflicts) in entries
                    when conflicts
                      collect `(let ((,package-variable (find-package ,name)))
                                 (dolist (,name-variable ',conflicts)
                                   (shadow ,name-variable ,package-variable))))))))))

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
