(require :asdf)
(let* ((root (uiop:pathname-parent-directory-pathname (uiop:pathname-directory-pathname *load-truename*)))
       (cache (merge-pathnames ".build/fresh-multiple-value-binding-fasl/" root)))
  (asdf:initialize-source-registry `(:source-registry (:directory ,root) :ignore-inherited-configuration))
  (asdf:initialize-output-translations `(:output-translations (t ,cache) :ignore-inherited-configuration)))
(asdf:load-system "snowgrave")
(load (merge-pathnames "artifact-functions.lisp" *load-truename*))
(assert (not (find-package "SNOWGRAVE.MULTIPLE-VALUE-BINDING.FIXTURE")))
(destructuring-bind (source metadata observations) (uiop:command-line-arguments)
  (multiple-value-bind (artifact warnings failure)
      (compile-file source :output-file (merge-pathnames ".build/fresh-multiple-value-binding.fasl"
                                                       (asdf:system-source-directory "snowgrave")))
    (declare (ignore warnings)) (assert (not failure)) (load artifact))
  (let* ((unit (with-open-file (stream metadata) (read stream)))
         (expected (with-open-file (stream observations) (read stream)))
         (package (find-package "SNOWGRAVE.MULTIPLE-VALUE-BINDING.FIXTURE"))
         (trace (find-symbol "*TRACE*" package))
         (record (funcall (snowgrave.artifact-tests:artifact-function unit "BOOT") 17)))
    (assert (not (find-class (find-symbol "NODE" package) nil)))
    (dolist (name '("AMOUNT" "PROJECT" "ESCAPE-PROJECT" "CALLBACK" "BOOT"
                    "METHOD-PACK" "RELAY" "PACK" "ESCAPE-PACK" "RECURSIVE-PACK"
                    "OPTIONAL-PACK" "KEY-PACK" "DEFAULT-ESCAPE-PACK" "ZERO-PACK"
                    "VARIABLE-PRIMARY" "VARIABLE-CALLABLE" "ARGUMENT-PACK"
                    "COMPARISON-PACK" "KEY-ARGUMENTS" "VIA-VALUES"
                    "VARIABLE-PACK" "ESCAPED-VARIABLE-PACK" "RECURSIVE-VARIABLE-PACK"))
      (assert (not (fboundp (find-symbol name package)))))
    (loop for cases in expected for i from 0
          for entry = (snowgrave.artifact-tests:artifact-function unit (format nil "ENTRY-~D" i)) do
      (dolist (case cases)
        (setf (symbol-value trace) nil)
        (assert (equal (second case) (multiple-value-list (funcall entry record (first case)))))
        (assert (equal (third case) (reverse (symbol-value trace))))))))
(assert (not (fboundp 'snowgrave.sbcl:close-source)))
(format t "Fresh explicit secondary bindings executed.~%")
