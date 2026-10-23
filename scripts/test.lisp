(require :asdf)
(let ((root (uiop:pathname-parent-directory-pathname
             (uiop:pathname-directory-pathname *load-truename*))))
  (asdf:load-asd (merge-pathnames "snowgrave.asd" root))
  (asdf:test-system "snowgrave"))
