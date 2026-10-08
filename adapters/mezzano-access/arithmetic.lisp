;;;; Shared target-only checked numeric lowering, extracted from Wonderworld 50a6fd6.
;;;; The lexical caller owns failure policy and full code/data/lifetime admission.
;;;; Generic numeric domains remain ordinary outside the owner's lexical scope.
(in-package #:snowgrave.mezzano-access)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *original-arithmetic-compiler-macros* (make-hash-table :test #'equal))

  (defun checked-binary-arithmetic (operator left right failure continuation)
    ;; Raw native add/subtract wraps to a tagged fixnum without allocating.
    ;; Reject signed overflow before publishing that wrapped result. These tests
    ;; use the sign of the actual encoded native fixnum, not host word arithmetic.
    (let ((result (gensym "RESULT")))
      `(let ((,result (,(if (eq operator '+)
                           'mezzano.compiler::%fast-fixnum-+
                           'mezzano.compiler::%fast-fixnum--) ,left ,right)))
         (if ,(if (eq operator '+)
                  `(or (not (eq (mezzano.runtime::%fixnum-< ,left 0)
                                (mezzano.runtime::%fixnum-< ,right 0)))
                       (eq (mezzano.runtime::%fixnum-< ,left 0)
                           (mezzano.runtime::%fixnum-< ,result 0)))
                  `(or (eq (mezzano.runtime::%fixnum-< ,left 0)
                           (mezzano.runtime::%fixnum-< ,right 0))
                       (eq (mezzano.runtime::%fixnum-< ,left 0)
                           (mezzano.runtime::%fixnum-< ,result 0))))
             ,(funcall continuation result)
             ,failure))))

  (defun fold-checked-arithmetic (operator first rest failure)
    (if (null rest) first
        (checked-binary-arithmetic
         operator first (car rest) failure
         (lambda (result) (fold-checked-arithmetic operator result (cdr rest) failure)))))

  (defun checked-binary-product (left right failure continuation)
    ;; IDIV on tagged operands gives an untagged quotient which the builtin
    ;; boxes. Divide only by nonzero values, and handle -1 separately so the
    ;; MIN/-1 quotient can never be boxed. Truncation toward zero gives precisely
    ;; the integer product boundary for each sign quadrant.
    (let ((limit (gensym "PRODUCT-LIMIT")) (remainder (gensym "REMAINDER")))
      `(cond ((or (eql ,left 0) (eql ,right 0)) ,(funcall continuation 0))
             ((eql ,right -1)
              ,(checked-binary-arithmetic '- 0 left failure continuation))
             (t
              (multiple-value-bind (,limit ,remainder)
                  (mezzano.runtime::%fixnum-truncate
                   (if (eq (mezzano.runtime::%fixnum-< ,left 0)
                           (mezzano.runtime::%fixnum-< ,right 0))
                       most-positive-fixnum most-negative-fixnum)
                   ,right)
                (declare (ignore ,remainder))
                (if (if (mezzano.runtime::%fixnum-< ,left 0)
                        (not (mezzano.runtime::%fixnum-< ,left ,limit))
                        (not (mezzano.runtime::%fixnum-< ,limit ,left)))
                    ,(funcall continuation `(mezzano.compiler::%fast-fixnum-* ,left ,right))
                    ,failure))))))

  (defun fold-checked-product (first rest failure)
    (if (null rest) first
        (checked-binary-product
         first (car rest) failure
         (lambda (result)
           ;; Freeze an intermediate once before it becomes the next receiver.
           (let ((value (gensym "PRODUCT")))
             `(let ((,value ,result))
                ,(fold-checked-product value (cdr rest) failure)))))))

  (defun fold-fixnum-bits (operator first rest)
    (if (null rest) first
        `(,(ecase operator
             (logand 'mezzano.runtime::%fixnum-logand)
             (logior 'mezzano.runtime::%fixnum-logior)
             (logxor 'mezzano.runtime::%fixnum-logxor))
          ,(fold-fixnum-bits operator first (butlast rest)) ,(car (last rest)))))

  (defun fixnum-comparison (operator left right)
    (case operator
      (< `(mezzano.runtime::%fixnum-< ,left ,right))
      (> `(mezzano.runtime::%fixnum-< ,right ,left))
      (<= `(not (mezzano.runtime::%fixnum-< ,right ,left)))
      (>= `(not (mezzano.runtime::%fixnum-< ,left ,right)))
      ;; Both values have passed the native FIXNUM tag guard. EQ is exact
      ;; numeric equality in that admitted domain and has a true backend builtin;
      ;; the ordinary EQL function includes other numeric domains and repair.
      (= `(eq ,left ,right))
      (/= `(not (eq ,left ,right)))))

  (defun fold-fixnum-extreme (operator first rest)
    (if (null rest) first
        (let ((value (gensym "EXTREME")))
          `(let ((,value (if (mezzano.runtime::%fixnum-< ,first ,(car rest))
                            ,(if (eq operator 'min) first (car rest))
                            ,(if (eq operator 'min) (car rest) first))))
             ,(fold-fixnum-extreme operator value (cdr rest))))))

  (defun emit-arithmetic (operator variables failure)
    (case operator
      (eql (if (= (length variables) 2) `(eq ,@variables) failure))
      (truncate
       (case (length variables)
         (1 `(values ,(first variables) 0))
         (2 (let ((number (first variables)) (divisor (second variables)))
              ;; For fixnums only MIN/-1 has an unrepresentable quotient. Admit
              ;; both hazards before IDIV or its quotient boxing, preserving
              ;; the native intrinsic's exact quotient and signed remainder.
              `(if (or (eq ,divisor 0)
                       (and (eq ,number most-negative-fixnum) (eq ,divisor -1)))
                   ,failure
                   (mezzano.runtime::%fixnum-truncate ,number ,divisor))))
         (otherwise failure)))
      (ash
       (if (= (length variables) 2)
           (let ((integer (first variables)) (count (second variables))
                 (result (gensym "SHIFT")))
             `(cond ((mezzano.runtime::%fixnum-< ,count 0)
                     (if (mezzano.runtime::%fixnum-< ,count -63)
                         (if (mezzano.runtime::%fixnum-< ,integer 0) -1 0)
                         (mezzano.runtime::%fixnum-right-shift
                          ,integer (mezzano.compiler::%fast-fixnum-- 0 ,count))))
                    ((eql ,integer 0) 0)
                    ((mezzano.runtime::%fixnum-< ,count 63)
                     (let ((,result (mezzano.compiler::%fast-fixnum-left-shift ,integer ,count)))
                       ;; Recovering the original signed value proves no bits
                       ;; were lost. Overlong dynamic x86 shifts are excluded
                       ;; before the machine's modulo-64 count can apply.
                       (if (eq ,integer (mezzano.runtime::%fixnum-right-shift ,result ,count))
                           ,result ,failure)))
                    (t ,failure)))
           failure))
      (+ (if variables (fold-checked-arithmetic '+ (car variables) (cdr variables) failure) 0))
      (* (if variables (fold-checked-product (car variables) (cdr variables) failure) 1))
      (- (cond ((null variables) failure)
               ((null (cdr variables))
                (checked-binary-arithmetic '- 0 (car variables) failure #'identity))
               (t (fold-checked-arithmetic '- (car variables) (cdr variables) failure))))
      ((1+ 1-)
       (if (= (length variables) 1)
           (checked-binary-arithmetic (if (eq operator '1+) '+ '-) (car variables) 1 failure #'identity)
           failure))
      ((plusp minusp zerop)
       (if (= (length variables) 1)
           (case operator
             (plusp `(mezzano.runtime::%fixnum-< 0 ,(car variables)))
             (minusp `(mezzano.runtime::%fixnum-< ,(car variables) 0))
             (zerop `(eql 0 ,(car variables))))
           failure))
      ((logand logior logxor)
       (if variables (fold-fixnum-bits operator (car variables) (cdr variables))
           (if (eq operator 'logand) -1 0)))
      (lognot (if (= (length variables) 1)
                  `(mezzano.runtime::%fixnum-logxor ,(car variables) -1) failure))
      ((evenp oddp)
       (if (= (length variables) 1)
           (let ((even `(eql 0 (mezzano.runtime::%fixnum-logand ,(car variables) 1))))
             (if (eq operator 'evenp) even `(not ,even)))
           failure))
      ((< <= > >= =)
       (if variables
           `(and ,@(loop for tail on variables while (cdr tail)
                         collect (fixnum-comparison operator (car tail) (cadr tail))))
           failure))
      (/= (if variables
              `(and ,@(loop for tail on variables append
                             (loop for right in (cdr tail) collect
                                   (fixnum-comparison '/= (car tail) right))))
              failure))
      ((min max) (if variables (fold-fixnum-extreme operator (car variables) (cdr variables)) failure))))

  (defun make-arithmetic-expander (name original)
    (lambda (form environment)
      (multiple-value-bind (failure admittedp)
          (admitted-access-failure environment)
        (if (not admittedp)
            (if original (funcall original form environment) form)
            (multiple-value-bind (arguments validp)
                (access-call-arguments form name)
              (if (not validp) form
                  (let ((variables (mapcar (lambda (argument) (declare (ignore argument)) (gensym "FIXNUM")) arguments)))
                    `(let ,(mapcar #'list variables arguments)
                       (if (and ,@(mapcar
                                   (lambda (variable)
                                     (if (eq name 'eql)
                                         ;; Exact EQL for fixnums, characters and
                                         ;; nonnumeric identity objects. Numeric
                                         ;; heap/immediate-float domains need a
                                         ;; separately admitted value operation.
                                         `(not (or (mezzano.internals::%value-has-immediate-tag-p
                                                    ,variable mezzano.internals::+immediate-tag-single-float+)
                                                   (mezzano.internals::%object-of-type-range-p
                                                    ,variable mezzano.internals::+first-numeric-object-tag+
                                                    mezzano.internals::+last-numeric-object-tag+)))
                                         `(mezzano.internals::fixnump ,variable)))
                                   variables))
                           ,(emit-arithmetic name variables failure)
                           ,failure)))))))))

  (defun install-arithmetic-accessors ()
    (dolist (name '(+ - * truncate ash 1+ 1- < <= > >= = /= eql min max plusp minusp zerop logand logior logxor lognot evenp oddp))
      (multiple-value-bind (original presentp) (gethash name *original-arithmetic-compiler-macros*)
        (unless presentp
          (setf original (compiler-macro-function name)
                (gethash name *original-arithmetic-compiler-macros*) original))
        (setf (compiler-macro-function name) (make-arithmetic-expander name original))))
    t)
  (install-arithmetic-accessors))
