(asdf:defsystem "snowgrave"
  :description "Portable closed-world CLOS source-to-artifact contracts"
  :author "Snowgrave contributors"
  :license "MIT"
  :version "0.1.0"
  :serial t
  :components ((:file "src/package")
               (:file "src/conditions")
               (:file "src/source")
               (:file "src/source-analysis")
               (:file "src/runtime")
               (:file "src/unit")
               (:file "src/mezzano-materializer"))
  :in-order-to ((asdf:test-op (asdf:test-op "snowgrave/tests"))))

(asdf:defsystem "snowgrave/sbcl"
  :description "Restricted two-pass SBCL source adapter for Snowgrave"
  :depends-on ("snowgrave")
  :serial t
  :components ((:file "src/sbcl-adapter")))

(asdf:defsystem "snowgrave/tests"
  :depends-on ("snowgrave/sbcl")
  :serial t
  :components ((:file "scripts/artifact-functions")
               (:file "tests/suite")
               (:file "tests/method-call-bindings")
               (:file "tests/vector-constants")
               (:file "tests/literal-identity")
               (:file "tests/predicate-refinement")
               (:file "tests/partition-factorization")
               (:file "tests/external-results")
               (:file "tests/external-value-guards")
               (:file "tests/fixed-generic-calls")
               (:file "tests/typed-slots")
               (:file "tests/native-materialization"))
  :perform (asdf:test-op (operation component)
             (declare (ignore operation component))
             (uiop:symbol-call :snowgrave.tests :run-tests)))

(asdf:defsystem "snowgrave/mezzano-access"
  :description "Independent cold Mezzano lowering for caller-admitted native access"
  :license "MIT"
  :serial t
  :components ((:module "adapters/mezzano-access" :if-feature :mezzano
                :serial t
                :components ((:file "scope") (:file "entries") (:file "records") (:file "arrays") (:file "arithmetic")))))

(asdf:defsystem "snowgrave/mezzano-materializer"
  :description "Cold typed record materialization of frozen CLOS source on Mezzano"
  :depends-on ("snowgrave" "snowgrave/mezzano-access")
  :license "MIT"
  :components ((:file "adapters/mezzano-materializer" :if-feature :mezzano)))
