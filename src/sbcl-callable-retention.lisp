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
        ;; Table presence retains the generic's whole partition. An empty
        ;; actual tuple set is not an arbitrary call or a dead-cell proof.
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

