(in-package #:snowgrave.sbcl)

(defun configured-callable-retention-p (build)
  (and (graph-state-profile-p build) (entry-rooted-deployment-p build)))

(defun retain-named-callable (build name)
  "Retain code and identity without manufacturing an invocation tuple."
  (if (and (configured-callable-retention-p build)
           (or (ordinary-function-form build name)
               (member-name name (getf (build-declaration build) :closed-generics))))
      (progn
        (unless (gethash name (build-function-values build))
          (if *collect-function-flow*
              (setf (gethash name (build-function-values build)) t
                    *function-flow-changed* t)
              (fail build 'snowgrave:incomplete-domain :callable-value-reachability
                    "A named callable lacks its cold retention proof." :reachability)))
        ;; Table presence retains the generic identity. Only the complete
        ;; caller fixed point can decide which runtime cells it requires.
        (when (and *collect-function-flow*
                   (member-name name (getf (build-declaration build) :closed-generics))
                   (not (nth-value 1 (gethash name (build-generic-call-shapes build)))))
          (setf (gethash name (build-generic-call-shapes build)) (make-hash-table :test #'equal)
                *function-flow-changed* t)))
      (audit-function-capture build name)))

(defun settle-retained-callables (build)
  ;; Keep the old arbitrary-body obligation for identity-only targets. A later
  ;; caller may overapproximate with that fallback; it never removes it.
  (dolist (name (loop for name being the hash-keys of (build-function-values build) collect name))
     (when (if (ordinary-function-form build name)
               (not (nth-value 1 (gethash name (build-function-domains build))))
               (zerop (hash-table-count (gethash name (build-generic-call-shapes build)))))
       (audit-function-capture build name))))

(defun generic-cell-has-admitted-input-p (build generic)
  ;; Analysis may provisionally visit fewer cells, then revisit them as inputs
  ;; widen. Deployment uses the settled table and repeats all call coverage
  ;; checks. Unknown/capture rows stay possible; no source writer is declared
  ;; unreachable merely because its body has not been visited.
  (or (not (configured-callable-retention-p build))
      (initialization-generic-p generic)
      (let ((shapes (gethash generic (build-generic-call-shapes build))))
        (when shapes
          (loop for key being the hash-keys of shapes using (hash-value input)
                thereis
                (destructuring-bind (capture variable-tail count literal-names &optional native-payloads) key
                  (declare (ignore literal-names native-payloads))
                  (or capture
                      (let ((domains (record-flow-positional-inputs input)))
                        ;; PENDING is bottom during the scratch solve. Its
                        ;; producer has not returned a value yet; it is not an
                        ;; arbitrary caller. Unsolved components are widened
                        ;; by the existing settlement owner before deployment.
                        (and (not (and *collect-function-flow*
                                       (some (lambda (domain) (eq (relational-base domain) :pending))
                                             (subseq domains 0 (min count (length *cell-domains*))))))
                             (generic-call-row-possible-p build domains variable-tail count))))))))))
