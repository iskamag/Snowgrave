(in-package #:snowgrave.sbcl)

;;;; Native argument parsing keeps malformed keys in conditions. Admission
;;;; consumes raw call facts before the binding owner discards those keys.
;;;; The emitted host lambda still owns parsing, defaults, errors and effects.

(defun generic-parser-contract (build gf applicable)
  "The same effective contract serves validator emission and payload admission."
  (let* ((contract (copy-list (lambda-contract build (sb-mop:generic-function-lambda-list gf))))
         (keywords (mapcar #'keyword-name (getf contract :keys)))
         (allow (getf contract :allow)))
    ;; A REST-only generic's ordinary validator has no KEY parser. In the
    ;; admitted host protocol, method KEY clauses do not turn that parser on.
    (when (getf contract :keyp)
      (dolist (method applicable)
        (let ((method-contract (lambda-contract build (sb-mop:method-lambda-list method))))
          (dolist (key (getf method-contract :keys)) (pushnew (keyword-name key) keywords))
          (when (getf method-contract :allow) (setf allow t)))))
    (setf (getf contract :accepted-keywords) keywords (getf contract :allow) allow)
    contract))

(defun parser-key-status (build domain name)
  (cond ((subtype-domain-p build domain (list 'eql name)) :equal)
        ((subtype-domain-p build domain (list 'not (list 'eql name))) :different)
        (t :maybe)))

(defun parser-allows-other-keys-p (build contract tail)
  (or (getf contract :allow)
      (loop for remaining on tail by #'cddr while (cdr remaining)
            for key = (first remaining) for value = (second remaining)
            do (case (parser-key-status build key :allow-other-keys)
                 (:equal (return (subtype-domain-p build value '(not null))))
                 ;; An earlier uncertain name could itself be the first AOK.
                 ;; A later literal occurrence cannot supply its value proof.
                 (:maybe (return nil))))))

(defun parser-accepted-key-p (build contract domain)
  (every (lambda (part)
           (some (lambda (key) (eq :equal (parser-key-status build part key)))
                 (cons :allow-other-keys
                       (or (getf contract :accepted-keywords)
                           (mapcar #'keyword-name (getf contract :keys))))))
         (domain-alternatives domain)))

(defun audit-lambda-parser-inputs (build contract supplied variable-tail owner &key native-payloads)
  "Admit only native/private-safe payloads on feasible actual KEY parser paths.
SUPPLIED is the raw ordered tuple, not projected parameter domains. Capture
envelopes are excluded by callers. This adds no runtime parser or checker."
  (when (and (graph-state-profile-p build) (not *collect-function-flow*)
             (getf contract :positional-surplus-p))
    (when variable-tail
      (fail build 'snowgrave:unclosed-call :graph-state-parser-tail
            (format nil "The unknown optional surplus of ~S lacks its native payload proof." owner)
            :reachability))
    (loop for domain in (nthcdr (min (length supplied) (length (lambda-positional-variables contract))) supplied)
          for position from (length (lambda-positional-variables contract))
          when (and (not (nth position native-payloads)) (graph-private-payload-domain-p build domain))
          do
        (fail build 'snowgrave:unclosed-call :graph-state-parser-payload
              (format nil "The optional parser of ~S can publish a private surplus operand in its native condition." owner)
              :reachability)))
  (when (and (graph-state-profile-p build) (not *collect-function-flow*) (getf contract :keyp))
    (let ((tail (nthcdr (min (length supplied) (length (lambda-positional-variables contract))) supplied)))
      (unless (parser-allows-other-keys-p build contract tail)
        (when variable-tail
          (fail build 'snowgrave:unclosed-call :graph-state-parser-tail
                (format nil "The unknown keyword tail of ~S lacks its native parser payload proof." owner)
                :reachability))
        ;; On this host an odd complete KEY tail signals its count error
        ;; before unknown-key rejection; that error retains no input operand.
        (unless (oddp (length tail))
          (loop for remaining on tail by #'cddr while (cdr remaining)
                for key = (first remaining)
                when (and (not (parser-accepted-key-p build contract key))
                          (graph-private-payload-domain-p build key))
                  do (fail build 'snowgrave:unclosed-call :graph-state-parser-payload
                           (format nil "The keyword parser of ~S can publish a private key operand in its native condition." owner)
                           :reachability)))))))

(defun audit-generic-parser-inputs (build generic contract)
  (when (and (graph-state-profile-p build) (not *collect-function-flow*))
    (map-generic-program-call-inputs
     build generic
     (lambda (domains variable-tail native-payloads)
       (audit-lambda-parser-inputs build contract domains variable-tail generic :native-payloads native-payloads)))))

(defun audit-method-positional-parser-inputs (build generic method)
  ;; This method's native binder, not the population of the generic, owns the
  ;; tail condition. The shared row iterator preserves actual cell guards;
  ;; capture placeholders do not fabricate execution of an error path.
  (let ((contract (lambda-contract build (sb-mop:method-lambda-list method) :method t)))
    (setf (getf contract :positional-surplus-p) t)
    (when (and (graph-state-profile-p build) (not *collect-function-flow*))
      (map-generic-program-call-inputs
       build generic (lambda (domains variable-tail native-payloads)
                       (audit-lambda-parser-inputs build contract domains variable-tail generic :native-payloads native-payloads))))))

(defun audit-apply-parser-tail (build form)
  ;; APPLY parses its own final operand before the callee's lambda parser.
  ;; This obligation is independent of KEY/AOK and of target retention.
  (when (and (graph-state-profile-p build) (not *collect-function-flow*))
    (multiple-value-bind (arguments bindings completep variable-tail)
        (ordinary-call-argument-plan build form :required-count 0)
      (declare (ignore arguments bindings))
      (let ((tail (car (last form))))
        (unless (or (and completep (not variable-tail))
                    (native-data-form-p build tail)
                    (graph-native-payload-form-p build tail))
          (fail build 'snowgrave:unclosed-call :graph-state-apply-tail
                "APPLY's native tail parser can publish this private operand before the callee runs."
                :reachability))))))
