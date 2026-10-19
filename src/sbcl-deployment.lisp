(in-package #:snowgrave.sbcl)

(defun entry-rooted-deployment-p (build)
  (eq (getf (build-declaration build) :deployment-roots) :entries))

(defun deployed-generics (build)
  ;; The declaration seals the complete authored world. In entry-rooted mode,
  ;; table presence records an actual call/capture dependency, even when its
  ;; normal argument-shape set is empty (for example, a short-arity call).
  (remove-if-not
   (lambda (name)
     (or (not (entry-rooted-deployment-p build))
         (and (build-generic-call-shapes build)
              (nth-value 1 (gethash name (build-generic-call-shapes build))))))
   (getf (build-declaration build) :closed-generics)))

(defun retain-construction-initialization (build)
  ;; Generated stock delegation is a real dependency, not an authored call
  ;; node in TRANSFORM-FORM. Reuse the capture owner conservatively: all
  ;; selected initialization cells remain audited, including custom methods.
  (when (entry-rooted-deployment-p build)
    (dolist (name '(initialize-instance shared-initialize))
      (when (member-name name (getf (build-declaration build) :closed-generics))
        (audit-generic-call-shape build name nil t nil)))))

(defun open-class-name-expression (build expression package local)
  ;; FIND-CLASS and CHANGE-CLASS accept symbolic designators. Preserve their
  ;; evaluation point and map only sealed source names into the disposable
  ;; world. Built-ins, foreign names and actual class objects keep host meaning.
  (let ((value (gensym "OPEN-CLASS-NAME-")))
    `(let ((,value ,(transform-form build expression package :open t :local local)))
       (cond ,@(mapcar (lambda (name)
                         `((eq ,value ',name) ',(mapped-name name package)))
                       (build-classes build))
             (t ,value)))))

(defun open-reflection-form (build form package local)
  ;; This code is compiled only in the disposable open world. Every reached
  ;; closed occurrence still goes through TRANSFORM-FORM's rejection branch.
  ;; No host metaobject, callable or operation is added to the deployed ABI.
  `(,(first form)
    ,@(loop for argument in (rest form) for position from 0
            collect (if (or (and (eq (first form) 'find-class) (= position 0))
                            (and (eq (first form) 'change-class) (= position 1)))
                        (open-class-name-expression build argument package local)
                        (transform-form build argument package :open t :local local)))))

(defun validate-generic-protocol (build generic gf)
  ;; One protocol owner for both source-universe admission and emitted code.
  (if (initialization-generic-p generic)
      (unless (and (eq (class-of gf) (find-class 'standard-generic-function))
                   (typep (sb-mop:generic-function-method-combination gf) 'sb-pcl::standard-method-combination))
        (fail build 'snowgrave:unclosed-class-operation :initialization-generic-protocol
              "Initialization generic classes and combinations require exact host normalization." :materialization))
      (progn
        (unless (eq (class-of gf) (find-class 'standard-generic-function))
          (fail build 'snowgrave:unsupported-definition :generic-function-class
                "Custom generic-function classes need an exact argument/applicability/error contract." :materialization))
        (unless (or (typep (sb-mop:generic-function-method-combination gf) 'sb-pcl::standard-method-combination)
                    (let ((name (source-generic-combination build generic)))
                      (or (authored-combination-name build name) (member name *host-method-combinations*))))
          (fail build 'snowgrave:unsupported-definition :custom-method-combination
                "Custom combinations need their own audited normalized source extension." :materialization)))))

(defun audit-sealed-generic-provenance (build)
  ;; Omitting runtime code does not omit source/MOP provenance. Inspect actual
  ;; methods without transforming their bodies or invoking custom CEM code.
  (dolist (name (getf (build-declaration build) :closed-generics))
    (let ((gf (open-generic build name)))
      (validate-generic-protocol build name gf)
      (if (initialization-generic-p name)
          (dolist (layout (build-layouts build))
            (initialization-methods build name
                                    (find-class (mapped-name (getf layout :class) (build-open-package build)))))
          (dolist (method (sb-mop:generic-function-methods gf))
            (unless (authored-method build name method)
              (fail build 'snowgrave:unsupported-definition :method-provenance
                    "A sealed generic method lacks authored or accessor provenance." :materialization)))))))

(defun deployment-evidence (build)
  (let* ((generics (deployed-generics build))
         (functions (remove-if-not
                     (lambda (name) (nth-value 1 (gethash name (build-function-domains build))))
                     (build-functions build)))
         (retained (append functions generics)))
    (list :root-policy (or (getf (build-declaration build) :deployment-roots) :selected)
          :public-entries (mapcar #'snowgrave::function-name-key
                                  (getf (build-declaration build) :entries))
          :sealed-source
          (mapcar (lambda (definition)
                    (list :source-key (list (build-identity build) (snowgrave:authored-definition-position definition))
                          :kind (snowgrave:authored-definition-kind definition)
                          :name-key (snowgrave::function-name-key (snowgrave:authored-definition-name definition))))
                  (snowgrave:authored-source-definitions (build-source build)))
          :sealed-classes (mapcar #'snowgrave::function-name-key (build-classes build))
          :sealed-generics (mapcar #'snowgrave::function-name-key
                                  (getf (build-declaration build) :closed-generics))
          :retained-callables (mapcar #'snowgrave::function-name-key retained)
          :omitted-callables
          (loop for name in (append (build-functions build) (getf (build-declaration build) :closed-generics))
                unless (member-name name retained)
                  collect (list :name-key (snowgrave::function-name-key name)
                                :reason :unreachable-from-deployment-roots))
          :proof :shared-call-capture-and-construction-fixed-point
          :cell-coverage :whole-sealed-partition-of-each-retained-generic)))
