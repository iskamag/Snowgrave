;;;; Cold lowering of actual sealed Mezzano record fields.
(in-package #:snowgrave.mezzano-access)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *original-record-compiler-macros* (make-hash-table :test #'equal))

  (defun record-call-arguments (form name count)
    ;; Compiler macros can see both ordinary calls and literal FUNCALL forms.
    ;; An unsupported call shape stays an ordinary call for the caller's code
    ;; admission audit to diagnose; it never silently acquires raw access.
    (multiple-value-bind (arguments recognizedp) (access-call-arguments form name)
      (if (and recognizedp (eql (length arguments) count))
          (values arguments t)
          (values nil nil))))

  (defun record-inline-identity-p (name record-name slot-name operation)
    ;; The native getter decoder alone ignores effects before its final slot
    ;; form. Check the actual generated getter/writer/CAS body as one contract.
    (let* ((inline (nth-value 1 (mezzano.compiler::function-inline-info name)))
           (finitep (handler-case (not (null (list-length inline))) (type-error () nil)))
           (arguments (and (consp inline) (second inline)))
           (block (and finitep (consp inline) (car (last inline))))
           (object (nth (ecase operation ((:read :predicate) 0) (:write 1) (:cas 2)) arguments))
           (slot `(mezzano.internals::%struct-slot ,object ',record-name ',slot-name)))
      (and finitep (consp inline) (eq (first inline) 'lambda)
           (handler-case (not (null (list-length arguments))) (type-error () nil))
           (= (length arguments) (ecase operation ((:read :predicate) 1) (:write 2) (:cas 3)))
           (every #'symbolp arguments)
           (every (lambda (prefix) (or (null prefix) (stringp prefix)
                                      (equal prefix `(declare (mezzano.internals::lambda-name ,name)))))
                  (butlast (cddr inline)))
           (equal block `(block ,(if (symbolp name) name (second name))
                          ,(ecase operation
                             (:read slot)
                             (:predicate `(typep ,object ',record-name))
                             (:write `(setf ,slot ,(first arguments)))
                             (:cas `(mezzano.internals::cas ,slot ,(first arguments) ,(second arguments)))))))))

  (defun record-slot-domain (type)
    ;; The actual finalized declaration owns this domain. Keywords and zero
    ;; have exact EQ/EQL native identity without any numeric/class fallback.
    ;; Retain a private finite copy, not a borrowed declaration cons list.
    (cond ((member type '(t fixnum)) (values type t))
          ((eq type 'bit) (values '(unsigned-byte 1) t))
          ((and (consp type) (member (car type) '(unsigned-byte signed-byte))
                (consp (cdr type)) (null (cddr type))
                (typep (second type) '(integer 1 32)))
           (values (copy-list type) t))
          ((and (consp type) (member (car type) '(member eql))
                (handler-case (not (null (list-length type))) (type-error () nil))
                (cdr type) (or (eq (car type) 'member) (null (cddr type)))
                (every (lambda (value) (or (keywordp value) (eql value 0))) (cdr type)))
           (values (cons 'member (copy-list (cdr type))) t))
          (t (values nil nil))))

  (defun record-domain-test (value domain)
    (cond ((eq domain t) t)
          ((eq domain 'fixnum) `(mezzano.internals::fixnump ,value))
          ((eq (car domain) 'unsigned-byte)
           `(and (mezzano.internals::fixnump ,value)
                 (mezzano.runtime::%fixnum-<-unsigned ,value ,(ash 1 (second domain)))))
          ((eq (car domain) 'signed-byte)
           (let ((limit (ash 1 (1- (second domain)))))
             `(and (mezzano.internals::fixnump ,value)
                   (not (mezzano.runtime::%fixnum-< ,value ,(- limit)))
                   (mezzano.runtime::%fixnum-< ,value ,limit))))
          (t `(or ,@(mapcar (lambda (literal) `(eq ,value ',literal)) (cdr domain))))))

  (defun make-record-access-expander (name header primitive index operation domain original)
    (lambda (form environment)
      (block expand
        (multiple-value-bind (failure admittedp) (admitted-access-failure environment)
          (unless admittedp (return-from expand (if original (funcall original form environment) form)))
          (multiple-value-bind (arguments validp)
              (record-call-arguments form name (ecase operation (:read 1) (:write 2) (:cas 3)))
            (if (not validp) form
                (let* ((object (gensym "RECORD")) (value (gensym "VALUE")) (old (gensym "OLD"))
                       (actual (gensym "ACTUAL")) (success (gensym "SUCCESS"))
                       (cas (if (eq primitive 'mezzano.internals::%object-ref-t)
                                `(multiple-value-bind (,success ,actual)
                                 (mezzano.internals::%cas-object ,object ',index ,old ,value)
                               (declare (ignore ,success))
                               ,(if (eq domain t) actual
                                    `(if ,(record-domain-test actual domain) ,actual ,failure)))
                                `(let ((,actual (funcall (function (mezzano.internals::cas ,primitive))
                                                        ,old ,value ,object ',index)))
                                   (if ,(record-domain-test actual domain) ,actual ,failure)))))
                  `(let ,(ecase operation
                           (:read `((,object ,(first arguments))))
                           (:write `((,value ,(first arguments)) (,object ,(second arguments))))
                           ;; Native CAS place expansion already evaluates the
                           ;; receiver before OLD/NEW. Its actual CAS function
                           ;; ABI is OLD, NEW, receiver; direct calls retain it.
                           (:cas `((,old ,(first arguments)) (,value ,(second arguments))
                                   (,object ,(third arguments)))))
                     (if (and (mezzano.internals::%value-has-tag-p ,object mezzano.internals::+tag-object+)
                              (mezzano.internals::%fast-instance-layout-eq-p ,object ',header))
                         ,(ecase operation
                            (:write (if (eq domain t) `(setf (,primitive ,object ',index) ,value)
                                        `(if ,(record-domain-test value domain)
                                             (setf (,primitive ,object ',index) ,value) ,failure)))
                            (:read (if (not (eq domain t))
                                       `(let ((,value (,primitive ,object ',index)))
                                          (if ,(record-domain-test value domain) ,value ,failure))
                                       `(,primitive ,object ',index)))
                            (:cas (if (not (eq domain t))
                                      `(if (and ,(record-domain-test old domain)
                                                ,(record-domain-test value domain)) ,cas ,failure)
                                      cas)))
                         ,failure)))))))))

  (defun install-record-accessors (record-name accessors)
    "Cold registration; inspect the actual finalized native/cross structure.
Exact sealed scalar boxed T/FIXNUM, finite keyword/zero MEMBER/EQL, BIT and
explicit signed/unsigned widths 1..32 are supported. Numeric storage uses the
actual native upgraded byte width and finalized byte offset. Full-width 64-bit
loads can allocate boxed bignums and are not admitted here. Ordinary DEFSTRUCT type/error
behavior remains in force outside the lexical admission marker."
    (unless (handler-case (not (null (list-length accessors))) (type-error () nil))
      (error "Record accessor declarations must be a finite proper list: ~S" record-name))
    (let* ((class (mezzano.internals::get-structure-type record-name))
           (layout (mezzano.clos:class-layout class))
           (slots (mezzano.clos:class-slots class)))
      (unless (and (mezzano.clos:class-sealed class) layout)
        (error "Record access requires a finalized sealed structure: ~S" record-name))
      (let ((header (mezzano.runtime::%make-instance-header layout))
            (plans nil))
        ;; Validate every requested field before publishing any compiler macro.
        (dolist (pair accessors)
          (unless (and (consp pair) (consp (cdr pair)) (null (cddr pair))
                       (symbolp (first pair)) (symbolp (second pair)))
            (error "Invalid record accessor declaration: ~S" pair))
          (let* ((name (first pair))
                 (slot (find (second pair) slots :key #'mezzano.clos:slot-definition-name)))
            (unless slot (error "No actual slot ~S in record ~S" (second pair) record-name))
            ;; Use the native compiler's existing accessor/source decoder. A
            ;; caller-supplied name/slot mismatch must not change a valid call.
            (multiple-value-bind (actual-record actual-slot)
                (mezzano.internals::struct-accessor-info name)
              (unless (and (eq actual-record record-name) (eq actual-slot (second pair)))
                (error "Accessor ~S does not read actual field ~S.~S" name record-name (second pair))))
            (dolist (operation (if (mezzano.clos:structure-slot-definition-read-only slot)
                                  '(:read) '(:read :write :cas)))
              (let ((function-name (ecase operation
                                     (:read name) (:write (list 'setf name))
                                     (:cas (list 'mezzano.internals::cas name)))))
                (unless (record-inline-identity-p function-name record-name (second pair) operation)
                  (error "Accessor ~S lacks the exact native ~S field identity." function-name operation))))
            (let* ((location (mezzano.clos:slot-definition-location slot))
                   (type (mezzano.runtime::location-type location))
                   (offset (mezzano.runtime::location-offset location))
                   (domain (record-slot-domain (mezzano.clos:slot-definition-type slot)))
                   (numericp (and (consp domain) (member (car domain) '(unsigned-byte signed-byte))))
                   (index (if numericp offset (mezzano.runtime::location-offset-t location)))
                   (accessor (mezzano.runtime::location-type-accessor type))
                   (primitive (if numericp
                                  (intern (concatenate 'string "%" (symbol-name accessor))
                                          (symbol-package accessor)) accessor)))
              (unless (and domain
                           (not (mezzano.clos:structure-slot-definition-fixed-vector slot))
                           (typep index 'fixnum) (<= 0 index)
                           (if numericp
                               (multiple-value-bind (expected size)
                                   (mezzano.internals::compute-struct-slot-accessor-and-size domain)
                                 (and (eql type expected) (zerop (mod offset size))
                                      (<= (+ offset size) (* 8 (mezzano.internals::layout-heap-size layout)))))
                               (and (eql type mezzano.runtime::+location-type-t+)
                                    (eq primitive 'mezzano.internals::%object-ref-t)
                                    (= (* index 8) offset)
                                    (< index (mezzano.internals::layout-heap-size layout)))))
                (error "Unsupported frozen record field ~S.~S at ~S" record-name (second pair) location))
              (push (list name header primitive index :read domain) plans)
              (unless (mezzano.clos:structure-slot-definition-read-only slot)
                (push (list (list 'setf name) header primitive index :write domain) plans)
                (push (list (list 'mezzano.internals::cas name) header primitive index :cas
                            domain) plans)))))
        (dolist (plan (nreverse plans))
          (multiple-value-bind (original presentp) (gethash (first plan) *original-record-compiler-macros*)
            (unless presentp
              (setf original (compiler-macro-function (first plan))
                    (gethash (first plan) *original-record-compiler-macros*) original))
            (setf (compiler-macro-function (first plan))
                  (apply #'make-record-access-expander (append plan (list original))))))))
    record-name)

  (defun make-record-predicate-expander (record-name name header original)
    (lambda (form environment)
      (block expand
        ;; This predicate has ordinary boolean semantics. Shape mismatch is
        ;; NIL, never the enclosing access failure action or a slot read.
        (unless (nth-value 1 (admitted-access-failure environment))
          (return-from expand (if original (funcall original form environment) form)))
        (multiple-value-bind (arguments validp) (record-call-arguments form name 1)
          (if (not validp) form
              (let ((object (gensym "RECORD")))
                ;; Catch changed cold definitions before emitting their code.
                ;; Runtime binding/layout retention remains the owner's duty.
                (unless (and (record-inline-identity-p name record-name nil :predicate)
                             (let ((class (mezzano.internals::get-structure-type record-name)))
                               (and (mezzano.clos:class-sealed class)
                                    (eq (mezzano.clos:class-layout class)
                                        (mezzano.runtime::%unpack-instance-header header)))))
                  (error "Record predicate ~S changed after cold registration." name))
                `(let ((,object ,(first arguments)))
                   (and (mezzano.internals::%value-has-tag-p ,object mezzano.internals::+tag-object+)
                        (mezzano.internals::%fast-instance-layout-eq-p ,object ',header)))))))))

  (defun install-record-predicate (record-name predicate)
    "Register an exact generated DEFSTRUCT predicate over its sealed layout.
Sealing forbids descendants and redefinition; an included sealed child still
has its own exact header. Slot contents and declared value types are irrelevant.
The owner must retain the actual predicate binding and layout lifetime."
    (unless (and (symbolp record-name) record-name (symbolp predicate) predicate)
      (error "Record predicate registration needs actual record/predicate names."))
    (let* ((class (mezzano.internals::get-structure-type record-name))
           (layout (mezzano.clos:class-layout class)))
      (unless (and (mezzano.clos:class-sealed class) layout)
        (error "Record predicate requires a finalized sealed structure: ~S" record-name))
      ;; A supplied name must be the actual generated TYPEP binding, including
      ;; its implicit block. Never erase effects or substitute another type.
      (unless (record-inline-identity-p predicate record-name nil :predicate)
        (error "Predicate ~S lacks exact native type identity ~S." predicate record-name))
      (multiple-value-bind (original presentp) (gethash predicate *original-record-compiler-macros*)
        (unless presentp
          (setf original (compiler-macro-function predicate)
                (gethash predicate *original-record-compiler-macros*) original))
        (setf (compiler-macro-function predicate)
              (make-record-predicate-expander record-name predicate
               (mezzano.runtime::%make-instance-header layout) original))))
    record-name)

  (defmacro define-record-accessors (record-name accessors)
    "Register scoped raw getters/writers/CAS after the real DEFSTRUCT definition.
ACCESSORS contains (ordinary-accessor-name actual-slot-name) pairs derived by
the DEFSTRUCT owner, including its :CONC-NAME choice. Cold registration must
precede compilation of admitted entry bodies. It allocates and can signal."
    `(eval-when (:compile-toplevel :load-toplevel :execute)
       (install-record-accessors ',record-name ',accessors)))

  (defmacro define-record-predicate (record-name predicate)
    "Register the actual DEFSTRUCT owner's predicate after its definition.
Only calls in WITH-ADMITTED-ACCESS use exact sealed-header lowering. Foreign
and immediate values return NIL; unsupported call syntax stays ordinary."
    `(eval-when (:compile-toplevel :load-toplevel :execute)
       (install-record-predicate ',record-name ',predicate))))
