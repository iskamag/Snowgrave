(defpackage #:snowgrave.coerce.fixture
  (:use #:cl)
  (:shadowing-import-from #:snowgrave #:defclass #:defgeneric #:defmethod))

(in-package #:snowgrave.tests)

(defvar *coerce-type-expansions* 0)
(deftype snowgrave.coerce.fixture::unadmitted-type ()
  (incf *coerce-type-expansions*)
  'vector)
(defun snowgrave.coerce.fixture::external-list () (list 1 2))

(defun sequence-coerce-unit (body identity domain &key external)
  (let* ((*package* (find-package :snowgrave.coerce.fixture))
         (entry (intern "ENTRY"))
         (form (read-from-string (format nil "(defun entry (input) ~A)" body))))
    (values
     (snowgrave:close-source-unit
      (list :forms (list form)) :unit-name identity
      :universe '(t list vector symbol number) :entries (list entry)
      :external-domains (list (list entry (list domain)))
      :external-operations (when external (list (intern "EXTERNAL-LIST"))))
     form)))

(defun sequence-coerce-positive-tests ()
  (let ((*package* (find-package :snowgrave.coerce.fixture)))
    (loop for body in '("(coerce input 'vector)"
                       "(funcall #'coerce input 'vector)"
                       "(apply #'coerce input (list 'vector))"
                       "(multiple-value-call #'coerce (values input 'vector))"
                       "(coerce (funcall #'coerce input 'vector) 'list)"
                       "(fill (funcall #'coerce input 'vector) 23)")
          for index from 1 do
      (multiple-value-bind (unit form)
          (sequence-coerce-unit body (list 'coerce-call :case index) 'list)
        (eval form)
        (dolist (input (list '(1 2 3) nil (list (list :shared) "text")))
          (let ((expected (funcall (intern "ENTRY") input))
                (actual (funcall (snowgrave:unit-function unit "ENTRY") input)))
            (check (equalp expected actual)))))))
  (loop for (body domain input) in
        '(("(coerce input 'string)" list (#\a #\b))
          ("(coerce input 'simple-bit-vector)" list (1 0 1))
          ("(coerce input '(vector (unsigned-byte 8)))" list (1 2 255))
          ("(coerce input '(simple-array bit (*)))" list (1 0 1))
          ("(coerce input 'list)" vector #(1 :two nil))
          ("(coerce input 'simple-vector)" vector "abc"))
        for index from 1 do
    (multiple-value-bind (unit form)
        (sequence-coerce-unit body (list 'coerce-target :case index) domain)
      (eval form)
      (check (equalp (funcall (second form) input)
                     (funcall (snowgrave:unit-function unit "ENTRY") input)))))
  ;; The ordinary host owns identity when the original already has the type.
  (dolist (domain '(list vector))
    (let* ((input (if (eq domain 'list) (list :a :b) (vector :a :b)))
           (unit (sequence-coerce-unit (format nil "(coerce input '~A)" domain)
                                       (list 'coerce-identity :domain domain) domain)))
      (check (eq input (funcall (snowgrave:unit-function unit "ENTRY") input)))))
  ;; Copying sequence shape preserves each native element's actual identity.
  (let* ((child (list :same-object))
         (input (make-array 4 :initial-contents (list child :b :hidden :hidden)
                              :fill-pointer 2 :adjustable t))
         (unit (sequence-coerce-unit "(coerce input 'list)" '(coerce-elements :version 1) 'vector))
         (result (funcall (snowgrave:unit-function unit "ENTRY") input)))
    (check (= (length result) 2))
    (check (eq (first result) child))))

(defun sequence-coerce-rejection-tests ()
  (loop for (body domain feature) in
        '(("(coerce input 'function)" symbol :coerce-target)
          ("(funcall #'coerce input 'function)" symbol :coerce-target)
          ("(coerce input 'unadmitted-type)" list :coerce-target)
          ("(coerce input '(vector unadmitted-type))" list :coerce-target)
          ("(coerce input input)" list :coerce-target)
          ("(sb-kernel:vector-to-list input)" vector :call-target)
          ("(replace input input)" vector :call-target)
          ("(coerce input 'vector)" t :coerce-sequence-domain)
          ("(coerce (external-list) 'vector)" list :coerce-sequence-domain)
          ("(coerce (the list (external-list)) 'vector)" list :coerce-sequence-domain)
          ("(progn input #'coerce)" list :ordinary-function-capture)
          ("(progn input #'fill)" list :ordinary-function-capture)
          ("(let ((convert #'coerce)) (funcall convert input 'vector))" list :ordinary-function-capture))
        for index from 1 do
    (let* ((identity (list 'coerce-refusal :case index))
           (condition
             (handler-case
                 (progn (sequence-coerce-unit body identity domain :external (search "external-list" body)) nil)
               (snowgrave:snowgrave-error (condition) condition))))
      (check (typep condition 'snowgrave:snowgrave-error))
      (check (eq (snowgrave:error-feature condition) feature))
      (check (equal (snowgrave:error-source-key condition) (list identity 1)))))
  (check (zerop *coerce-type-expansions*)))

(defun sequence-coerce-record-element-tests ()
  (let* ((*package* (find-package :snowgrave.coerce.fixture))
         (forms (read-from-string
                 "((defclass cell () ())
                   (defun boot () (make-instance 'cell))
                   (defun entry (object)
                     (let* ((vector (coerce (list object) 'vector))
                            (list (coerce vector 'list)))
                       (values (eq object (car list))
                               (typep (aref vector 0) 'cell)))))"))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(coerce-record-elements :version 1)
                :closed-classes (list (intern "CELL")) :universe (list (intern "CELL") 't)
                :entries (mapcar #'intern '("BOOT" "ENTRY"))
                :external-domains (list (list (intern "BOOT") nil)
                                        (list (intern "ENTRY") (list (intern "CELL"))))))
         (object (funcall (snowgrave:unit-function unit "BOOT"))))
    (check (equal '(t t) (multiple-value-list
                          (funcall (snowgrave:unit-function unit "ENTRY") object))))))

(defun sequence-coerce-multiple-value-tests ()
  ;; The same exact ordered-value owner handles helper producers and literal
  ;; VALUES. Zero-value producers still execute in their original order.
  (let* ((*package* (find-package :snowgrave.coerce.fixture))
         (forms (read-from-string
                 "((defparameter *order* nil)
                   (defun before () (push :before *order*) (values))
                   (defun produce (input) (push :data *order*) (values input 'list))
                   (defun after () (push :after *order*) (values))
                   (defun entry (input)
                     (let ((*order* nil))
                       (let ((result
                               (fill (multiple-value-call #'coerce
                                       (before) (produce input) (after)) 17)))
                         (values result (reverse *order*))))))"))
         (entry (intern "ENTRY"))
         (unit (snowgrave:close-source-unit
                (list :forms forms) :unit-name '(coerce-helper-producers :version 1)
                :universe '(t list vector symbol number) :entries (list entry)
                :external-domains (list (list entry '(vector))))))
    (dolist (form forms) (eval form))
    (dolist (input (list #(1 2 3) #()))
      (check (equal (multiple-value-list (funcall entry input))
                    (multiple-value-list (funcall (snowgrave:unit-function unit entry) input)))))))

(defun sequence-coerce-scaling-tests ()
  ;; Count cold analysis visits, not timing. Opaque shared MVC position facts
  ;; must prevent a second traversal of each literal producer's input subtree.
  (let* ((build (snowgrave.sbcl::make-build
                 :identity '(coerce-analysis-scaling)
                 :source (snowgrave:make-authored-source nil :identity '(coerce-analysis-scaling))))
         (raw (fdefinition 'snowgrave.sbcl::raw-value-domain))
         (visits 0))
    (unwind-protect
         (progn
           (setf (fdefinition 'snowgrave.sbcl::raw-value-domain)
                 (lambda (build form) (incf visits) (funcall raw build form)))
           (dolist (origin '(vector :external-result))
             (dolist (depth '(8 32 64))
               (let ((form 'input)
                     (snowgrave.sbcl::*argument-domains* (list (cons 'input origin))))
                 (dotimes (index depth)
                   (setf form `(multiple-value-call #'coerce (values ,form 'vector))))
                 (setf visits 0)
                 (check (eq origin (snowgrave.sbcl::value-domain build form)))
                 (check (<= visits (+ (* 5 depth) 5)))))))
      (setf (fdefinition 'snowgrave.sbcl::raw-value-domain) raw))))

(defun sequence-coerce-tests ()
  (let ((*coerce-type-expansions* 0))
    (sequence-coerce-positive-tests)
    (sequence-coerce-rejection-tests)
    (sequence-coerce-record-element-tests)
    (sequence-coerce-multiple-value-tests)
    (sequence-coerce-scaling-tests)))
