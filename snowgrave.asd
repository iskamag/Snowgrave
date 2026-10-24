(asdf:defsystem "snowgrave"
  :description "MOP composition, class-to-struct lowering, and closed source recompilation"
  :author "Snowgrave contributors"
  :license "MIT"
  :depends-on ("closer-mop" "cl-form-types")
  :serial t
  :components ((:file "src/package")
               (:file "src/host-normalization")
               (:file "src/hosts/sbcl" :if-feature :sbcl)
               (:file "src/hosts/ccl" :if-feature :ccl)
               (:file "src/walker")
               (:file "src/source")
               (:file "src/rewrite")
               (:file "src/normalize")
               (:file "src/records")
               (:file "src/metadata")
               (:file "src/observation")
               (:file "src/composition")
               (:file "src/methods")
               (:file "src/unit")
               (:file "src/configuration")
               (:file "src/specialize"))
  :in-order-to ((asdf:test-op (asdf:test-op "snowgrave/tests"))))

(asdf:defsystem "snowgrave/sbcl" :depends-on ("snowgrave"))

(asdf:defsystem "snowgrave/host-tools"
  :components ((:file "support/host")))

(asdf:defsystem "snowgrave/tests"
  :depends-on ("snowgrave" "snowgrave/host-tools")
  :serial t
  :components ((:file "tests/host") (:file "tests/core") (:file "tests/overhead") (:file "tests/configuration") (:file "tests/portability"))
  :perform (asdf:test-op (operation component)
             (declare (ignore operation component))
             (uiop:symbol-call :snowgrave.tests :run-tests)))
