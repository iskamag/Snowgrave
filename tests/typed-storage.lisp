(in-package #:snowgrave.tests)

;; Compare physical storage decisions with the host's own DEFSTRUCT, rather
;; than assuming that every declared numeric type has an unboxed representation.
#+sbcl
(defstruct native-typed-storage
  (u8 0 :type (unsigned-byte 8))
  (u64 0 :type (unsigned-byte 64))
  (signed 0 :type (signed-byte 64))
  (single 0f0 :type single-float)
  (double 0d0 :type double-float)
  (short 0s0 :type short-float)
  (long 0l0 :type long-float)
  (complex #c(0d0 0d0) :type (complex double-float))
  (positive 1 :type (integer 1 9))
  (positive-float 1d0 :type (double-float (0d0) 9d0)))

(defun typed-storage-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :typed-storage
       "((defclass holder ()
            ((u8 :type (unsigned-byte 8))
             (u64 :type (unsigned-byte 64))
             (signed :type (signed-byte 64))
             (single :type single-float)
             (double :type double-float)
             (short :type short-float)
             (long :type long-float)
             (complex :type (complex double-float))
             (positive :type (integer 1 9))
             (positive-float :type (double-float (0d0) 9d0))
             (ref :type node)
             (peer :type holder)
             (empty :type nil)))
          (defclass node () ())
          (defclass leaf (node) ())
          (defun construct () (make-instance 'holder))
          (defun entry ()
            (let ((o (construct)))
              (setf (slot-value o 'u8) 255
                    (slot-value o 'u64) 18446744073709551615
                    (slot-value o 'signed) -9223372036854775808
                    (slot-value o 'single) 1.5f0
                    (slot-value o 'double) 2.5d0
                    (slot-value o 'short) (coerce 1 'short-float)
                    (slot-value o 'long) (coerce 1 'long-float)
                    (slot-value o 'complex) #c(1d0 2d0)
                    (slot-value o 'positive) 7
                    (slot-value o 'positive-float) 3d0
                    (slot-value o 'ref) (make-instance 'leaf)
                    (slot-value o 'peer) o)
              (values (slot-value o 'u8) (slot-value o 'u64)
                      (slot-value o 'signed) (slot-value o 'single)
                      (slot-value o 'double) (slot-value o 'complex)
                      (slot-value o 'short) (slot-value o 'long)
                      (slot-value o 'positive) (slot-value o 'positive-float)
                      (not (null (typep (slot-value o 'ref) 'node)))
                      (eq o (slot-value o 'peer)))))
          (defun unbind ()
            (let ((o (construct)))
              (setf (slot-value o 'double) 2d0 (slot-value o 'positive) 7
                    (slot-value o 'ref) (make-instance 'node))
              (mapc (lambda (name) (slot-makunbound o name))
                    '(double positive ref peer empty))
              (values (slot-boundp o 'double) (slot-boundp o 'positive)
                      (slot-boundp o 'ref) (slot-boundp o 'peer)
                      (slot-boundp o 'empty))))
          (defun restart-read ()
            (let ((o (construct)))
              (values (handler-bind ((unbound-slot
                                      (lambda (c) (declare (ignore c))
                                        (invoke-restart 'use-value :not-a-float))))
                        (slot-value o 'double))
                      (slot-boundp o 'double))))
          (defun reject ()
            (let ((o (construct)))
              (setf (slot-value o 'positive) 7)
              (values (handler-case (setf (slot-value o 'positive) 0)
                        (type-error () :rejected))
                      (slot-value o 'positive)
                      (handler-case (setf (slot-value o 'positive-float) 0d0)
                        (type-error () :rejected))
                      (slot-boundp o 'positive-float)
                      (handler-case (setf (slot-value o 'ref) nil)
                        (type-error () :rejected))
                      (slot-boundp o 'ref)))))"
       "(construct entry unbind restart-read reject)"
       "((construct ()) (entry ()) (unbind ()) (restart-read ()) (reject ()))" "()")
    (compare-entry unit package "ENTRY" nil
                   '((255 18446744073709551615 -9223372036854775808
                      1.5f0 2.5d0 #c(1d0 2d0) 1s0 1l0 7 3d0 t t) nil))
    (compare-entry unit package "UNBIND" nil '((nil nil nil nil nil) nil))
    (compare-entry unit package "RESTART-READ" nil '((:not-a-float nil) nil)
                   :native-p #-ecl t #+ecl nil)
    ;; Invalid CLOS writes are not a portable differential oracle. Check the
    ;; closed contract: private unbound placeholders never become valid stores.
    (check (equal '((:rejected 7 :rejected nil :rejected nil) nil)
                  (observed-call (snowgrave:unit-function unit (find-symbol "REJECT" package)) nil))
           "Typed storage admitted an unbound placeholder as a logical value")
    #+sbcl
    (let* ((plan (snowgrave::closed-unit-plan unit))
           (layout (find (find-symbol "HOLDER" package) (snowgrave::unit-plan-layouts plan)
                         :key #'snowgrave::class-description-name))
           (physical (sb-kernel:dd-slots
                      (sb-kernel:find-defstruct-description (snowgrave::class-description-type layout))))
           (native (sb-kernel:dd-slots (sb-kernel:find-defstruct-description 'native-typed-storage))))
      (dolist (expected native)
        (let* ((slot (find (symbol-name (sb-kernel:dsd-name expected))
                           (snowgrave::class-description-slots layout)
                           :key (lambda (slot) (symbol-name (snowgrave::slot-description-name slot)))
                           :test #'string=))
               (actual (find (snowgrave::slot-description-field slot) physical :key #'sb-kernel:dsd-name)))
          (check (and (not (eq (sb-kernel:dsd-type actual) t))
                      (equal (sb-kernel:dsd-raw-type expected) (sb-kernel:dsd-raw-type actual)))
                 "Slot ~S differs from native storage: ~S versus ~S"
                 (sb-kernel:dsd-name expected) actual expected))))))

(defun typed-method-tests ()
  (multiple-value-bind (unit package)
      (make-fixture
       :typed-methods
       "((defclass base () ((value :initform 7 :type integer)))
          (defclass child (base) ((value :type (integer 1 9))))
          (defgeneric read-value (o))
          (defmethod read-value ((o base)) (slot-value o 'value))
          (defgeneric step-value (n))
          (defmethod step-value ((n fixnum)) (1+ n))
          (defmethod step-value ((n double-float)) (+ n 1d0))
          (defgeneric keyword-method (n &key replace))
          (defmethod keyword-method ((n fixnum) &key (replace (progn (setq n (1+ n)) t)))
            (values n replace))
          (defun entry () (read-value (make-instance 'child)))
          (defun numeric (n) (step-value n))
          (defun floating (n) (step-value n))
          (defun reassigned () (keyword-method 7))
          (defun inherited-reject ()
            (let ((o (make-instance 'child)))
              (handler-case (setf (slot-value o 'value) 10)
                (type-error () :rejected)))))"
       "(entry numeric floating reassigned inherited-reject)"
       "((entry ()) (numeric (fixnum)) (floating (double-float)) (reassigned ()) (inherited-reject ()))"
       "(read-value step-value keyword-method)" :universe "(fixnum double-float)")
    (compare-entry unit package "ENTRY" nil '((7) nil))
    (compare-entry unit package "NUMERIC" '(41) '((42) nil))
    (compare-entry unit package "FLOATING" '(1d0) '((2d0) nil))
    (compare-entry unit package "REASSIGNED" nil '((8 t) nil))
    (check (eq :rejected (funcall (snowgrave:unit-function unit (find-symbol "INHERITED-REJECT" package))))
           "Typed storage lost the inherited type intersection")
    (check (= 42 (funcall (snowgrave:bind-entry unit (find-symbol "NUMERIC" package) '(41))))
           "Method specializer widened a known configured argument")
    (check (= 2d0 (funcall (snowgrave:bind-entry unit (find-symbol "FLOATING" package) '(1d0))))
           "Configured floating method lost its argument type")
    (check (some (lambda (definition)
                   (and (eq (first definition) 'defun)
                        (let ((declaration (fourth definition)))
                          (and (consp declaration) (eq (first declaration) 'declare)
                               (find 'fixnum (rest declaration) :key #'second)))))
                 (snowgrave:unit-source unit))
           "Generated numeric method lost its compiler-visible specializer")))
