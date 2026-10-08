(defpackage #:snowgrave
  (:use #:common-lisp)
  (:shadow #:defclass #:defgeneric #:defmethod)
  (:export
   #:defclass #:defgeneric #:defmethod #:close-source-unit
   #:snowgrave-error #:unsupported-definition #:unclosed-call
   #:unclosed-class-operation #:nonreproducible-source #:mop-failure
   #:incomplete-domain #:residual-metaobject #:audit-failure
   #:error-source-key #:error-feature #:error-phase #:error-path #:error-detail
   #:domain-violation #:violation-unit #:violation-name #:violation-arguments
   #:closed-unit #:closed-unit-p #:unit-metadata #:unit-source
   #:unit-function #:unit-report #:write-unit-source #:write-unit-metadata
   #:make-layout #:layout-identity #:sg-make-record #:sg-record-p
   #:sg-record-class #:sg-record-typep #:sg-record-unit-p #:sg-record-layout-p #:sg-record-boundp #:sg-record-read
   #:sg-record-write #:sg-record-unbind #:sg-domain-violation
   #:write-mezzano-unit-source #:register-source-adapter
   #:source-name-key #:source-defining-kind #:make-authored-source #:authored-source
   #:authored-source-forms #:authored-source-definitions #:authored-source-names
   #:authored-source-kind-forms #:authored-source-specials #:find-authored-definition
   #:authored-form-position #:authored-definition #:authored-definition-kind
   #:authored-definition-name #:authored-definition-form #:authored-definition-position
   #:source-lambda-contract #:source-body-special-domains #:source-body-parts #:source-block-body
   #:analyze-source-bindings #:analyze-source-lambda-bindings #:source-required-binding-variables))

(defpackage #:snowgrave.class-identities
  (:use))

(defpackage #:snowgrave.sbcl
  (:use #:common-lisp)
  (:export #:close-source))

(defpackage #:snowgrave.mezzano-materializer
  (:use #:common-lisp)
  (:export #:define-materialized-unit #:native-unit-layouts #:admit-supervisor-unit))
