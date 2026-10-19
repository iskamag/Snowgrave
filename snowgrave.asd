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
               (:file "src/native-bindings")
               (:file "src/unit")
               (:file "src/mezzano-materializer"))
  :in-order-to ((asdf:test-op (asdf:test-op "snowgrave/tests"))))

(asdf:defsystem "snowgrave/sbcl"
  :description "Restricted two-pass SBCL source adapter for Snowgrave"
  :depends-on ("snowgrave")
  :serial t
  :components ((:file "src/sbcl-adapter")
               (:file "src/sbcl-configuration")
               (:file "src/sbcl-initialization")
               (:file "src/sbcl-relational")
               (:file "src/sbcl-deployment")
               (:file "src/sbcl-parser-inputs")
               (:file "src/sbcl-cold-source")))

(asdf:defsystem "snowgrave/tests"
  :depends-on ("snowgrave/sbcl")
  :serial t
  :components ((:file "scripts/artifact-functions")
               (:file "tests/suite")
               (:file "tests/method-call-bindings")
               (:file "tests/macro-normalization")
               (:file "tests/annotation-forms")
               (:file "tests/authored-combinations")
               (:file "tests/vector-constants")
               (:file "tests/literal-identity")
               (:file "tests/native-literal-graphs")
               (:file "tests/predicate-refinement")
               (:file "tests/partition-factorization")
               (:file "tests/external-results")
               (:file "tests/external-value-guards")
               (:file "tests/fixed-generic-calls")
               (:file "tests/optional-generic-calls")
               (:file "tests/generic-required-domains")
               (:file "tests/typed-slots")
               (:file "tests/closed-reference-slots")
               (:file "tests/layout-matching")
               (:file "tests/sequence-fill")
               (:file "tests/sequence-coerce")
               (:file "tests/sequence-shape")
               (:file "tests/native-aggregate-results")
               (:file "tests/immediate-callees")
               (:file "tests/selected-method-roots")
               (:file "tests/indirect-result-owners")
               (:file "tests/lambda-opaque-inputs")
               (:file "tests/local-function-flow")
               (:file "tests/pending-multiple-values")
               (:file "tests/cold-source-boundary")
               (:file "tests/cold-symbol-initializers")
               (:file "tests/deployment-roots")
               (:file "tests/cold-method-combinations")
               (:file "tests/open-host-operations")
               (:file "tests/cold-integer-initializers")
               (:file "tests/slot-place-normalization")
               (:file "tests/entry-graphs")
               (:file "tests/native-binding-contexts")
               (:file "tests/graph-state-inference")
               (:file "tests/private-containers")
               (:file "tests/constructor-state")
               (:file "tests/callable-payloads")
               (:file "tests/generic-error-authority")
               (:file "tests/place-update-inputs")
               (:file "tests/parser-inputs")
               (:file "tests/initialization-phase")
               (:file "tests/relational-state")
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
