;;;; Cold scoped array lowering for Mezzano's actual vector/header ABI.
;;;; Placement, lifetime, concurrent mutation exclusion and reachable values are
;;;; caller admission obligations. Boxed T, packed BIT and signed/unsigned 8/16/32-bit storage are supported.
(in-package #:snowgrave.mezzano-access)

(eval-when (:compile-toplevel :load-toplevel :execute)
  ;; Capture originals once. Repeated cross/native compile/load registration
  ;; replaces our wrapper instead of stacking wrappers around previous wrappers.
  (defvar *original-array-compiler-macros* (make-hash-table :test #'equal))

  (defun array-tag-test (object tag)
    `(and (mezzano.internals::%value-has-tag-p ,object mezzano.internals::+tag-object+)
          (mezzano.runtime::%%object-of-type-p ,object ,tag)))

  (defun admitted-array-element-layouts ()
    ;; Cold representation data only; no runtime callback/dispatch bank.
    ;; Tag and scaled access primitive are the actual native array ABI.
    '((mezzano.internals::+object-tag-array-t+ t mezzano.internals::%object-ref-t)
      (mezzano.internals::+object-tag-array-bit+ (unsigned-byte 1) :bit)
      (mezzano.internals::+object-tag-array-unsigned-byte-8+ (unsigned-byte 8) mezzano.internals::%%object-ref-unsigned-byte-8)
      (mezzano.internals::+object-tag-array-unsigned-byte-16+ (unsigned-byte 16) mezzano.internals::%%object-ref-unsigned-byte-16)
      (mezzano.internals::+object-tag-array-unsigned-byte-32+ (unsigned-byte 32) mezzano.internals::%%object-ref-unsigned-byte-32)
      (mezzano.internals::+object-tag-array-signed-byte-8+ (signed-byte 8) mezzano.internals::%%object-ref-signed-byte-8)
      (mezzano.internals::+object-tag-array-signed-byte-16+ (signed-byte 16) mezzano.internals::%%object-ref-signed-byte-16)
      (mezzano.internals::+object-tag-array-signed-byte-32+ (signed-byte 32) mezzano.internals::%%object-ref-signed-byte-32)))

  (defun emit-supported-array (object failure continuation &key complex-only)
    "CONTINUATION is a cold generator receiving storage/capacity/fill/domain/primitive."
    (let ((storage (gensym "STORAGE")) (capacity (gensym "CAPACITY"))
          (fill (gensym "FILL")) (info (gensym "INFO")))
      `(cond
         ,@(unless complex-only
             (loop for (tag domain primitive) in (admitted-array-element-layouts)
                   collect `(,(array-tag-test object (symbol-value tag))
                             ,(funcall continuation object
                               `(mezzano.internals::%object-header-data ,object) nil domain primitive))))
         ((and ,(array-tag-test object mezzano.internals::+object-tag-array+)
               (eql (mezzano.internals::%object-header-data ,object) 1))
          (let ((,storage (mezzano.internals::%object-ref-t ,object mezzano.internals::+complex-array-storage+))
                (,capacity (mezzano.internals::%object-ref-t ,object mezzano.internals::+complex-array-axis-0+))
                (,fill (mezzano.internals::%object-ref-t ,object mezzano.internals::+complex-array-fill-pointer+))
                (,info (mezzano.internals::%object-ref-t ,object mezzano.internals::+complex-array-info+)))
            (if (and (null ,info)
                     (or ,@(loop for (tag) in (admitted-array-element-layouts)
                                  collect (array-tag-test storage (symbol-value tag))))
                     (mezzano.internals::fixnump ,capacity)
                     (not (mezzano.runtime::%fixnum-<-unsigned
                           (mezzano.internals::%object-header-data ,storage) ,capacity))
                     (or (null ,fill)
                         (and (mezzano.internals::fixnump ,fill)
                              (not (mezzano.runtime::%fixnum-<-unsigned ,capacity ,fill)))))
                (cond ,@(loop for (tag domain primitive) in (admitted-array-element-layouts)
                              collect `(,(array-tag-test storage (symbol-value tag))
                                        ,(funcall continuation storage capacity fill domain primitive)))
                      (t ,failure))
                ,failure)))
         (t ,failure))))

  (defun emit-array-element (operation storage index value domain primitive failure &optional old)
    (when (eq operation :cas)
      (return-from emit-array-element
        (cond ((eq primitive :bit) failure) ; Native BIT CAS is unsupported.
              ((eq primitive 'mezzano.internals::%object-ref-t)
               (let ((success (gensym "SUCCESS")) (actual (gensym "ACTUAL")))
                 `(multiple-value-bind (,success ,actual)
                      (mezzano.internals::%cas-object ,storage ,index ,old ,value)
                    (declare (ignore ,success)) ,actual)))
              (t `(if (and ,(record-domain-test old domain) ,(record-domain-test value domain))
                      (funcall (function (mezzano.internals::cas ,primitive)) ,old ,value ,storage ,index)
                      ,failure)))))
    (let ((access (if (eq primitive :bit)
                      ;; Read one byte, never a boxed full 64-bit array word.
                      ;; x86 native BIT arrays use little-endian low-bit-first words.
                      `(mezzano.runtime::%fixnum-logand
                        (mezzano.runtime::%fixnum-right-shift
                         (mezzano.internals::%%object-ref-unsigned-byte-8
                          ,storage (mezzano.runtime::%fixnum-right-shift ,index 3))
                         (mezzano.runtime::%fixnum-logand ,index 7)) 1)
                      `(,primitive ,storage ,index))))
      (if (eq operation :read) access
          `(if ,(record-domain-test value domain)
               ,(if (eq primitive :bit)
                    (let ((byte-index (gensym "BYTE")) (shift (gensym "SHIFT")) (mask (gensym "MASK")))
                      `(let* ((,byte-index (mezzano.runtime::%fixnum-right-shift ,index 3))
                              (,shift (mezzano.runtime::%fixnum-logand ,index 7))
                              (,mask (mezzano.compiler::%fast-fixnum-left-shift 1 ,shift)))
                         ;; Exclusive mutation is part of the caller's admission;
                         ;; this ordinary AREF store is not an atomic BIT update.
                         (setf (mezzano.internals::%%object-ref-unsigned-byte-8 ,storage ,byte-index)
                               (mezzano.runtime::%fixnum-logior
                                (mezzano.runtime::%fixnum-logand
                                 (mezzano.internals::%%object-ref-unsigned-byte-8 ,storage ,byte-index)
                                 (mezzano.runtime::%fixnum-logxor ,mask -1))
                                (mezzano.compiler::%fast-fixnum-left-shift ,value ,shift)))
                         ,value))
                    `(setf ,access ,value))
               ,failure))))

  (defun emit-array-operation (operation variables failure)
    ;; VECTORP observes representation/rank only. It must retain the native
    ;; predicate's full domain, including specialized, string, displaced and
    ;; memory vectors; backing-storage admission belongs to actual access.
    (when (eq operation :vectorp)
      (let ((object (first variables)))
        (return-from emit-array-operation
          `(and (mezzano.internals::%value-has-tag-p ,object mezzano.internals::+tag-object+)
                (or (mezzano.runtime::%%object-of-type-range-p
                     ,object mezzano.internals::+first-simple-1d-array-object-tag+
                     mezzano.internals::+last-simple-1d-array-object-tag+)
                    (and (mezzano.runtime::%%object-of-type-range-p
                          ,object mezzano.internals::+first-complex-array-object-tag+
                          mezzano.internals::+last-complex-array-object-tag+)
                         (eql (mezzano.internals::%object-header-data ,object) 1)))))))
    (let* ((writerp (member operation '(:write :fill-write)))
           (casp (eq operation :cas))
           (object (nth (cond (casp 2) (writerp 1) (t 0)) variables))
           (value (cond (casp (second variables)) (writerp (first variables))))
           (index (nth (cond (casp 3) (writerp 2) (t 1)) variables)))
      (emit-supported-array
       object failure
       (lambda (storage capacity fill domain primitive)
         (case operation
           (:size capacity)
           (:length `(or ,fill ,capacity))
           (:fill `(if ,fill ,fill ,failure))
           (:fill-write
            `(if (and ,fill (mezzano.internals::fixnump ,value)
                      (not (mezzano.runtime::%fixnum-<-unsigned ,capacity ,value)))
                 (setf (mezzano.internals::%object-ref-t
                        ,object mezzano.internals::+complex-array-fill-pointer+) ,value)
                 ,failure))
           ((:read :write :cas)
            `(if (and (mezzano.internals::fixnump ,index)
                      (mezzano.runtime::%fixnum-<-unsigned ,index ,capacity))
                 ,(emit-array-element operation storage index value domain primitive failure (first variables))
                 ,failure))))
       :complex-only (member operation '(:fill :fill-write)))))

  (defun make-array-expander (name operation argument-count original)
    (lambda (form environment)
      (multiple-value-bind (failure admittedp)
          (admitted-access-failure environment)
        (if (not admittedp)
            (if original (funcall original form environment) form)
            (multiple-value-bind (arguments validp) (access-call-arguments form name)
              (if (not validp) form
                  (let ((count (length arguments))
                        (variables (mapcar (lambda (argument) (declare (ignore argument)) (gensym "ARG")) arguments)))
                    `(let ,(mapcar #'list variables arguments)
                       ,(if (eql count argument-count)
                            (emit-array-operation operation variables failure)
                            failure)))))))))

  (defun install-array-accessors ()
    (dolist (plan '((aref :read 2) ((setf aref) :write 3)
                    ((mezzano.internals::cas aref) :cas 4)
                    (mezzano.internals::aref-1 :read 2) ((setf mezzano.internals::aref-1) :write 3)
                    ((mezzano.internals::cas mezzano.internals::aref-1) :cas 4)
                    (length :length 1) (array-total-size :size 1) (vectorp :vectorp 1)
                    (fill-pointer :fill 1) ((setf fill-pointer) :fill-write 2)))
      (destructuring-bind (name operation count) plan
        (multiple-value-bind (original presentp) (gethash name *original-array-compiler-macros*)
          (unless presentp
            (setf original (compiler-macro-function name)
                  (gethash name *original-array-compiler-macros*) original))
          (setf (compiler-macro-function name) (make-array-expander name operation count original)))))
    t)

  (install-array-accessors))
