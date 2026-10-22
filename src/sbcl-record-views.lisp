(in-package #:snowgrave.sbcl)

;;;; A field's optional fourth item is a finite CURRENT class view:
;;;; ((exact-sealed-class boundness value-domain) ...).  The first three
;;;; items remain the unconditional field proof.  This is compiler data only.
;;;; A missing slot has :ABSENT boundness, not an unbound instance slot.

(defun record-view-domain-p (domain)
  ;; The empty list of exact layouts is known empty, not unknown or bottom.
  (and (consp domain) (eq (first domain) :record-view-classes)))

(defun record-view-classes (build domain)
  ;; Exact current coverage is independent of field values and provenance.
  ;; Nominal LEFT can include a sealed subclass; an actual LEFT layout need
  ;; not. Never recover this distinction from optional per-field cases.
  (cond ((member domain '(nil :pending :unknown :external-result)) nil)
        ((record-view-domain-p domain) (rest domain))
        ((relational-value-domain-p domain) (record-view-classes build (third domain)))
        ((and (consp domain) (eq (first domain) 'or))
         (when (every (lambda (part) (record-view-classes build part)) (rest domain))
           (remove-duplicates (loop for part in (rest domain) append (record-view-classes build part))
                              :test #'name= :from-end t)))
        ((initialization-domain-record domain)
         (let ((record (initialization-domain-record domain)))
           (if (sixth record) (record-view-classes build (sixth record))
               (generic-error-private-classes build domain))))
        (t (generic-error-private-classes build domain))))

(defun record-view-domain (build domain)
  (cond ((or (record-view-domain-p domain) (eq domain :pending)) domain)
        ((relational-value-domain-p domain) (record-view-domain build (third domain)))
        ((and (initialization-domain-record domain) (sixth (initialization-domain-record domain)))
         (sixth (initialization-domain-record domain)))
        (t (let ((classes (record-view-classes build domain)))
             (if classes (cons :record-view-classes classes) :unknown)))))

(defun record-flow-row-view-domain (build row &optional domain)
  (or (fifth row) (record-view-domain build (or (third row) domain))))

(defun merge-record-view-domains (build left right)
  (cond ((eq left :pending) right) ((eq right :pending) left)
        ((and (record-view-domain-p left) (record-view-domain-p right))
         (cons :record-view-classes
               (remove-duplicates
                (append (record-view-classes build left) (record-view-classes build right))
                :test #'name= :from-end t)))
        (t :unknown)))

(defun record-view-slot-p (build class slot)
  (member slot (getf (find class (build-layouts build) :key (lambda (row) (getf row :class)) :test #'name=) :slots)))

(defun record-view-domain-possible-p (build class domain)
  (cond ((eq domain :pending) nil)
        ((or (null domain) (member domain '(:unknown :external-result))) t)
        ((record-view-domain-p domain)
         (member-name class (rest domain)))
        ((record-view-classes build domain)
         (member-name class (record-view-classes build domain)))
        (t (some (lambda (part)
                   (or (member part '(:unknown :external-result))
                       (member-name class (record-view-classes build part))))
                 (domain-alternatives (relational-base domain))))))

(defun select-record-view-domain (build domain projected cell axis)
  (if (not (record-view-domain-p domain)) domain
      (cons :record-view-classes
            (remove-if-not (lambda (class)
                             (if axis (ordered-private-class-cell-p build class cell axis)
                                 (record-view-domain-possible-p build class projected)))
                           (rest domain)))))

(defun record-view-domain-covered-p (build actual expected)
  (declare (ignore build))
  (or (eq expected :unknown) (eq actual :pending)
      (and (record-view-domain-p actual) (record-view-domain-p expected)
           (every (lambda (class) (member-name class (rest expected))) (rest actual)))))

(defun record-field-cases (build slot field domain)
  (loop for class in (record-view-classes build domain)
        collect (or (assoc class (fourth field) :test #'name=)
                    (if (record-view-slot-p build class slot)
                        (list class (second field) (if field (third field) :external-result))
                        (list class :absent :external-result)))))

(defun merge-record-field-cases (build slot left right left-domain right-domain)
  (let* ((a (record-field-cases build slot left left-domain))
         (b (record-field-cases build slot right right-domain))
         (classes (remove-duplicates (append (mapcar #'first a) (mapcar #'first b))
                                     :test #'name= :from-end t)))
    (loop for class in classes
          for x = (assoc class a :test #'name=) for y = (assoc class b :test #'name=)
          collect
          (cond ((and (null x) (not (record-view-domain-possible-p build class left-domain))) (copy-tree y))
                ((and (null y) (not (record-view-domain-possible-p build class right-domain))) (copy-tree x))
                (t
                 (setf x (or x (if (record-view-slot-p build class slot)
                                   (list class (second left) (if left (third left) :external-result))
                                   (list class :absent :external-result)))
                       y (or y (if (record-view-slot-p build class slot)
                                   (list class (second right) (if right (third right) :external-result))
                                   (list class :absent :external-result))))
                 (list class (cond ((eq (second x) :pending) (second y))
                                   ((eq (second y) :pending) (second x))
                                   ((eq (second x) (second y)) (second x)))
                       (merge-value-domains build (third x) (third y))))))))

(defun map-record-field-cases (cases function)
  (mapcar (lambda (entry) (list (first entry) (second entry) (funcall function (third entry)))) cases))

(defun record-field-case-summary (build cases)
  (let ((status (reduce (lambda (old entry)
                          (let ((new (second entry)))
                            (cond ((eq old :pending) new) ((eq new :pending) old)
                                  ((eq old new) old))))
                        cases :initial-value :pending)))
    (values (if (eq status :absent) nil status)
            (reduce (lambda (old entry) (merge-value-domains build old (third entry)))
                    cases :initial-value :pending))))

(defun select-record-field-view (build field domain &optional cell axis)
  ;; No initial graph is consulted here. Restrict only the current proof.
  (let* ((cases (fourth field))
         (selected (remove-if-not
                    (lambda (entry)
                      (if axis
                          (ordered-private-class-cell-p build (first entry) cell axis)
                          (record-view-domain-possible-p build (first entry) domain))) cases)))
    (if (and cases selected)
        (multiple-value-bind (bound value) (record-field-case-summary build selected)
          (list (first field) bound value selected))
        (list (first field) (second field) (third field)))))

(defun record-field-cases-covered-p (build actual expected actual-domain)
  (or (null (fourth expected))
      (and (record-view-domain-p actual-domain) (null (rest actual-domain)))
      (let ((cases (record-field-cases build (first expected) actual actual-domain)))
        (and cases
             (every (lambda (a)
                      (let ((e (assoc (first a) (fourth expected) :test #'name=)))
                        (and e (or (null (second e)) (eq (second a) (second e)))
                             (record-flow-domain-covered-p build (third a) (third e)))))
                    cases)))))

(defun settle-record-field-cases (build input)
  (declare (ignore build))
  (when (record-flow-input-p input)
    (dolist (row (record-flow-input-records input))
      (dolist (field (second row))
        (dolist (entry (fourth field))
          (when (or (eq (second entry) :pending) (eq (third entry) :pending))
            (setf (second entry) nil (third entry) :external-result *function-flow-changed* t))))))
  input)

(defun set-record-field-cases (field cases)
  (if (cdddr field) (setf (fourth field) cases)
      (setf (cdddr field) (list cases)))
  field)
