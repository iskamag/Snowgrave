(require :asdf)
(let* ((root (uiop:pathname-parent-directory-pathname
              (uiop:pathname-directory-pathname *load-truename*)))
       (cache (merge-pathnames ".build/fasl/" root)))
  (asdf:initialize-source-registry `(:source-registry (:directory ,root) :ignore-inherited-configuration))
  (asdf:initialize-output-translations `(:output-translations (t ,cache) :ignore-inherited-configuration)))
(asdf:test-system "snowgrave")
