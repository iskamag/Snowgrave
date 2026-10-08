(load (merge-pathnames "mezzano-materializer-environment.lisp" *load-truename*))
(assert (not (find-package "WONDERWORLD")))
(assert (not (find-package "THREST")))
(dolist (name '("scope" "entries" "records" "arrays" "arithmetic"))
  (mezzano.compiler::load-for-cross-compiler
   (merge-pathnames (format nil "adapters/mezzano-access/~A.lisp" name) *leaf-root*) :verbose nil :print nil))

(dolist (path '("src/package.lisp" "src/conditions.lisp" "adapters/mezzano-materializer.lisp" ".build/native-authored-unit.lisp" ".build/native-authored-other-unit.lisp"))
  (mezzano.compiler::load-for-cross-compiler (merge-pathnames path *source-root*) :verbose nil :print nil))
(let ((mezzano.compiler::*target-architecture* :x86-64)
      (cross-cl:*features* (cons :x86-64 cross-cl:*features*)))
  (dolist (path '("src/package.lisp" "src/conditions.lisp" "adapters/mezzano-access/scope.lisp"
                  "adapters/mezzano-access/entries.lisp" "adapters/mezzano-access/records.lisp"
                  "adapters/mezzano-access/arrays.lisp" "adapters/mezzano-access/arithmetic.lisp"
                  "adapters/mezzano-materializer.lisp" ".build/native-authored-unit.lisp" ".build/native-authored-other-unit.lisp"))
    (let ((output (merge-pathnames (format nil "~A.llf" (pathname-name path)) *probe-cache*)))
      (ensure-directories-exist output)
      (let ((assembly (with-output-to-string (out)
                        (let ((*standard-output* out) (mezzano.compiler::*trace-asm* t))
                          (mezzano.compiler::cross-compile-file (merge-pathnames path *source-root*)
                            :output-file output :verbose nil :print nil)))))
        (with-open-file (out (make-pathname :type "lap" :defaults output)
                             :direction :output :if-exists :supersede)
          (write-string assembly out)))))
  (with-open-file (in (merge-pathnames "native-authored-unit.lap" *probe-cache*))
    (let ((assembly (make-string (file-length in))))
      (read-sequence assembly in)
      (dolist (forbidden '("(:NAMED-CALL SNOWGRAVE:SG-MAKE-RECORD"
                           "(:NAMED-CALL SNOWGRAVE:SG-RECORD"
                           "(:NAMED-CALL SNOWGRAVE::%RECORD"))
        (assert (not (search forbidden assembly))))))
  (let ((layouts (snowgrave.mezzano-materializer:native-unit-layouts '(:native-authored-typed))))
    (dolist (layout layouts)
      (format t "GENERATED-AUTHORED-NATIVE-LAYOUT ~S CPL=~S bytes=~D~%"
              (getf layout :class) (getf layout :ancestors) (getf layout :payload-bytes))
      (dolist (field (getf layout :fields))
        (format t "GENERATED-AUTHORED-FIELD ~S type=~S byte=~D boundbyte=~D mask=~D~%"
                (getf field :name) (getf field :type) (getf field :byte-offset)
                (getf field :bound-offset) (getf field :mask))))))
(format t "MEZZANO-AUTHORED-MATERIALIZER-CROSS-PASSED~%")
