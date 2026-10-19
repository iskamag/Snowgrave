;;;; Cold descriptor/header mapping and cross-compilation only.
(load (merge-pathnames "mezzano-materializer-environment.lisp" *load-truename*))
(dolist (path '("adapters/mezzano-access/scope.lisp" "adapters/mezzano-access/entries.lisp"
                "adapters/mezzano-access/records.lisp" "adapters/mezzano-access/arrays.lisp"
                "adapters/mezzano-access/arithmetic.lisp" "src/package.lisp" "src/conditions.lisp"
                "adapters/mezzano-materializer.lisp" "tests/native-layout-proof.lisp"))
  (mezzano.compiler::load-for-cross-compiler
   (merge-pathnames path *source-root*) :verbose nil :print nil))
(let* ((rows (snowgrave.mezzano-materializer:native-unit-layouts '(:native-layout-proof)))
       (row (first rows))
       (arguments (list (list 'quote (getf row :identity)) (list 'quote (getf row :class))
                        (list 'quote (getf row :ancestors)) (list 'quote (getf row :slots))
                        :slot-types (list 'quote (getf row :slot-types))
                        :error-mapping (list 'quote (getf row :error-mapping)))))
  (assert (eq row (snowgrave.mezzano-materializer::admitted-logical-layout arguments rows)))
  (dolist (change '(:identity :slots :slot-types :family))
    (let ((changed (copy-tree arguments)))
      (ecase change
        (:identity (setf (first changed) ''(:foreign)))
        (:slots (setf (fourth changed) ''(other-slot)))
        (:slot-types (setf (sixth changed) ''(fixnum)))
        (:family (setf changed (append changed '(:reference-domain unproved-family)))))
      (assert (handler-case
                  (progn (snowgrave.mezzano-materializer::admitted-logical-layout changed rows) nil)
                (error () t))))))
(let* ((mezzano.compiler::*target-architecture* :x86-64)
       (cross-cl:*features* (cons :x86-64 cross-cl:*features*))
       (assembly (with-output-to-string (out)
                   (let ((*standard-output* out) (mezzano.compiler::*trace-asm* t))
                     (mezzano.compiler::cross-compile-file
                      (merge-pathnames "tests/native-layout-proof.lisp" *source-root*)
                      :output-file (merge-pathnames "native-layout-proof.llf" *probe-cache*)
                      :verbose nil :print nil)))))
  (dolist (forbidden '("(:NAMED-CALL SNOWGRAVE:SG-RECORD-MATCHES-LAYOUT-P"
                       "(:NAMED-CALL SNOWGRAVE:MAKE-LAYOUT"))
    (assert (not (search forbidden assembly)))))
(format t "NATIVE LAYOUT PROOF CROSS-CHECKED; no native execution or supervisor admission claimed.~%")
