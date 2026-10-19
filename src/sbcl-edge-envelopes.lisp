(in-package #:snowgrave.sbcl)

;;;; Cold inductive fields for one installed configuration. Capture rows stay
;;;; immutable; the ordinary caller fixed point owns these separate premises.
;;;; Each internal field cell is (global-boundp value-domain fallbackp). Joins
;;;; weaken boundness independently of the monotone value-domain envelope.

(defstruct graph-field-write source-key slot unbindp state)

(defun register-graph-field-write (build site slot unbindp)
  (let ((entries (gethash site (build-graph-field-writes build))))
    (unless (find (build-source-key build) entries :key #'graph-field-write-source-key :test #'equal)
      (push (make-graph-field-write :source-key (build-source-key build) :slot slot :unbindp unbindp)
            (gethash site (build-graph-field-writes build))))))

(defun captured-field-domain (build domain)
  ;; A saved field selector denotes its saved value, never a later reread.
  (let ((persistent (persistent-record-flow-domain domain)))
    (if (external-value-observation-p build persistent) :external-result persistent)))

(defun initialize-graph-field-envelopes (build)
  (clrhash (build-graph-field-envelopes build))
  (let ((invalidations (build-graph-state-invalidations build)))
    (dolist (row (build-graph-nodes build))
      (when (getf row :class)
        (dolist (field (getf row :slots))
          (let* ((slot (first field)) (value (third field))
                 (forcedp (not (null (member slot (getf invalidations :forced-writes)))))
                 (status (if (member slot (getf invalidations :forced-unbinds)) nil (second field))))
            (when (member slot (getf invalidations :writes))
              (setf value (captured-field-domain build value)))
            (when forcedp (setf value (merge-value-domains build value :unknown)))
            (setf (gethash (list (getf row :id) slot) (build-graph-field-envelopes build))
                  (list status value forcedp))))))))

(defun graph-field-envelope (build domain slot)
  (let ((origin (persistent-record-flow-domain domain)))
    (when (graph-node-domain-p origin)
      (gethash (list (second origin) slot) (build-graph-field-envelopes build)))))

(defun begin-graph-field-iteration (build)
  (maphash (lambda (site writes)
             (declare (ignore site))
             (dolist (write writes) (setf (graph-field-write-state write) nil)))
           (build-graph-field-writes build)))

(defun join-graph-field-envelope (build field status value &optional fallbackp)
  (let* ((new-status (and (eq (first field) t) (eq status t)))
         (new-value (merge-value-domains build (second field) value))
         (fallback (or fallbackp (third field))))
    (unless (and (eq new-status (first field)) (equal new-value (second field)) (eq fallback (third field)))
      (unless *collect-function-flow*
        (fail build 'snowgrave:incomplete-domain :graph-field-envelope-coverage
              "A final store exceeds the settled configured field envelope." :reachability))
      (setf (first field) new-status (second field) new-value (third field) fallback
            *function-flow-changed* t))))

(defun fallback-graph-field-slot (build slot unbindp)
  ;; Unknown targets preserve the old conservative slot-wide obligation. This
  ;; selects affected fields; it supplies no class-wide replacement identity.
  (maphash (lambda (key field)
             (when (eq (second key) slot)
               (join-graph-field-envelope build field (and (not unbindp) (first field))
                                         :unknown t)))
           (build-graph-field-envelopes build)))

(defun pending-graph-field-domain-p (domain)
  (or (eq domain :pending)
      (and (consp domain) (eq (first domain) 'or)
           (some #'pending-graph-field-domain-p (rest domain)))))

(defun note-graph-field-write (build site receiver slot status value)
  "Publish a completed store prefix using its saved receiver/RHS receipts."
  (when (graph-state-profile-p build)
    (let* ((write (find (build-source-key build) (gethash site (build-graph-field-writes build))
                        :key #'graph-field-write-source-key :test #'equal))
           (target (persistent-record-flow-domain receiver))
           (stored (captured-field-domain build value))
           (parts (domain-alternatives target)))
      (when write
        (cond ((or (pending-graph-field-domain-p target)
                   (and (eq status t) (pending-graph-field-domain-p stored)))
               (unless (eq (graph-field-write-state write) :unsafe)
                 (setf (graph-field-write-state write) :pending)))
              ((every (lambda (part) (and (graph-node-domain-p part)
                                         (getf (graph-node-row build part) :class))) parts)
               (unless (member (graph-field-write-state write) '(:unsafe :pending))
                 (setf (graph-field-write-state write) :covered))
               ;; MAY targets get joins, never a destructive assignment. The
               ;; initial and all other prefix states remain in each envelope.
               (dolist (part parts)
                 (let ((field (graph-field-envelope build part slot)))
                   (when field
                     (join-graph-field-envelope build field status
                                               (if (eq status t) stored (second field)))))))
              ;; An exact fresh family cannot mutate an existing captured
              ;; object. Its own state remains with the constructor owner.
              ((every (lambda (part) (or (owned-record-domain-p part)
                                         (not (graph-private-record-domain-p build part)))) parts)
               (unless (member (graph-field-write-state write) '(:unsafe :pending))
                 (setf (graph-field-write-state write) :covered)))
              (t (setf (graph-field-write-state write) :unsafe)
                 (fallback-graph-field-slot build slot (not (eq status t)))))))))

(defun settle-graph-field-envelopes (build)
  ;; A visited prefix from an earlier narrow iteration is not full coverage.
  ;; Only the current settled replay discharges each complete-source site.
  (maphash (lambda (site writes)
             (declare (ignore site))
             (dolist (write writes)
               (unless (eq (graph-field-write-state write) :covered)
                 (fallback-graph-field-slot build (graph-field-write-slot write)
                                           (graph-field-write-unbindp write)))))
           (build-graph-field-writes build)))
