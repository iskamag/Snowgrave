;;;; Own archived native source only: MAKE-IMAGE writes its cold build directory.
(load (merge-pathnames "mezzano-materializer-probe.lisp" *load-truename*))
(let* ((runtime-llf (merge-pathnames "materializer-runtime.llf" *probe-cache*))
       (loader (merge-pathnames "materializer-loader.lisp" *probe-cache*))
       (mezzano.compiler::*target-architecture* :x86-64)
       (cross-cl:*features* (cons :x86-64 cross-cl:*features*)))
  (mezzano.compiler::load-for-cross-compiler
    (merge-pathnames ".build/native-authored-entry-names.lisp" *source-root*) :verbose nil :print nil)
  (assert (cross-cl:macro-function (find-symbol "ENTRY" "SNOWGRAVE.NATIVE-AUTHORED-RUNTIME")))
  (mezzano.compiler::cross-compile-file
    (merge-pathnames ".build/native-authored-entry-names.lisp" *source-root*)
    :output-file (merge-pathnames "native-authored-entry-names.llf" *probe-cache*) :verbose nil :print nil)
  (mezzano.compiler::cross-compile-file
   (merge-pathnames "tests/mezzano-materializer-runtime.lisp" *source-root*)
   :output-file runtime-llf :verbose nil :print nil)
  (with-open-file (out loader :direction :output :if-exists :supersede)
    (write-line "(in-package :mezzano.internals)" out)
    ;; Ordinary cold namespace setup from the artifact's own serializer. LLF
    ;; symbol objects must resolve before its initialization function executes.
    (with-open-file (in (merge-pathnames ".build/native-authored-unit.lisp" *source-root*))
      (loop for form = (read in nil in) until (eq form in)
            until (and (consp form) (eq (car form) 'snowgrave.mezzano-materializer:define-materialized-unit))
            do (let ((*print-readably* nil) (*print-escape* t))
                 (write form :stream out) (terpri out))))
    (dolist (name '("package" "conditions" "scope" "entries" "records" "arrays" "arithmetic" "mezzano-materializer" "native-authored-unit" "native-authored-other-unit" "native-authored-entry-names" "materializer-runtime"))
      (let ((bytes (with-open-file (in (merge-pathnames (format nil "~A.llf" name) *probe-cache*)
                                      :element-type '(unsigned-byte 8))
                     (let ((data (make-array (file-length in) :element-type '(unsigned-byte 8))))
                       (assert (= (read-sequence data in) (length data))) data))))
        (let ((*print-readably* t) (*print-length* nil) (*print-level* nil))
          (format out "(mezzano.internals::load-llf (mezzano.internals::mini-vector-stream ~S) t)~%" (coerce bytes 'simple-vector)))))
    (write-line "(snowgrave.native-authored-runtime:run)" out))
  ;; Compilation ends in this process. The image serializer consumes only the
  ;; completed LLFs in a fresh ordinary host process, so compiler proof objects
  ;; cannot remain accidental image-build roots.
  (mezzano.compiler::cross-compile-file loader
    :output-file (make-pathname :type "llf" :defaults loader) :verbose nil :print nil)
  (format t "SNOWGRAVE-MATERIALIZER-ARTIFACTS-COMPILED~%"))
