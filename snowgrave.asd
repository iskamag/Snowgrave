(asdf:defsystem "snowgrave"
  :description "MOP composition, class-to-struct lowering, and closed source recompilation"
  :author "Snowgrave contributors"
  :license "MIT"
  :serial t
  :components ((:file "src/package")
               (:file "src/source")
               (:file "src/rewrite")
               (:file "src/normalize")
               (:file "src/records")
               (:file "src/methods")
               (:file "src/unit"))
  :in-order-to ((asdf:test-op (asdf:test-op "snowgrave/tests"))))

(asdf:defsystem "snowgrave/sbcl" :depends-on ("snowgrave"))

(asdf:defsystem "snowgrave/tests"
  :depends-on ("snowgrave")
  :serial t
  :components ((:file "tests/core"))
  :perform (asdf:test-op (operation component)
             (declare (ignore operation component))
             (uiop:symbol-call :snowgrave.tests :run-tests)))
