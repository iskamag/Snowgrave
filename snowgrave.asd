(asdf:defsystem "snowgrave"
  :description "MOP composition, class-to-struct lowering, and closed source recompilation"
  :author "Snowgrave contributors"
  :license "MIT"
  :depends-on ("closer-mop" "cl-form-types")
  :serial t
  :components ((:file "src/package")
               (:file "src/plans")
               (:file "src/build")
               (:file "src/host-normalization")
               (:file "src/hosts/sbcl" :if-feature :sbcl)
               (:file "src/hosts/ccl" :if-feature :ccl)
               (:file "src/walker")
               (:file "src/literals")
               (:file "src/source")
               (:file "src/admission")
               (:file "src/rewrite")
               (:file "src/normalize")
               (:file "src/records")
               (:file "src/metadata")
               (:file "src/observation")
               (:file "src/usage")
               (:file "src/composition")
               (:file "src/method-abi")
               (:file "src/methods")
               (:file "src/dispatch")
               (:file "src/functions")
               (:file "src/artifact")
               (:file "src/unit")
               (:file "src/configuration")
               (:module "src/specialization"
                :serial t
                :components ((:file "facts")
                             (:file "bindings")
                             (:file "calls")
                             (:file "forms")))
               (:file "src/configuration-entry"))
  :in-order-to ((asdf:test-op (asdf:test-op "snowgrave/tests"))))

(asdf:defsystem "snowgrave/sbcl" :depends-on ("snowgrave"))

(asdf:defsystem "snowgrave/host-tools"
  :components ((:file "support/host")))

(asdf:defsystem "snowgrave/tests"
  :depends-on ("snowgrave" "snowgrave/host-tools")
  :serial t
  :components ((:file "tests/framework")
               (:file "tests/host")
               (:file "tests/methods")
               (:file "tests/records")
               (:file "tests/typed-storage")
               (:file "tests/source")
               (:file "tests/artifacts")
               (:file "tests/rejections")
               (:file "tests/overhead")
               (:file "tests/configuration")
               (:file "tests/portability")
               (:file "tests/lifecycle")
               (:file "tests/run"))
  :perform (asdf:test-op (operation component)
             (declare (ignore operation component))
             (uiop:symbol-call :snowgrave.tests :run-tests)))
