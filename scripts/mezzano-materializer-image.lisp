;;;; Consume completed native LLFs without retaining the compilation process.
(load (merge-pathnames "mezzano-materializer-environment.lisp" *load-truename*))
(let* ((loader (merge-pathnames "materializer-loader.lisp" *probe-cache*))
       (llf (make-pathname :type "llf" :defaults loader))
       (cold-generator::*warm-source-files*
         (append (remove "ipl.lisp" cold-generator::*warm-source-files* :test #'equal)
                 (list (namestring loader))))
       (*default-pathname-defaults* *native-source*))
  (assert (and (probe-file llf) (> (file-write-date llf) (file-write-date loader))))
  (cold-generator::make-image (merge-pathnames "materializer-image" *probe-cache*)
                             :image-size (* 5 1024 1024 1024)
                             :header-path (merge-pathnames "tools/disk-header.bin" *native-source*))
  (format t "SNOWGRAVE-MATERIALIZER-PRIVATE-IMAGE-BUILT~%"))
