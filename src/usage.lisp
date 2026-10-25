(in-package #:snowgrave)

;;; Which runtime helpers the owned source can reach. The closed emitter adds a
;;; helper only when an admitted call needs it; the scan is conservative, so a
;;; quoted or computed designator keeps the general path.

(defstruct (usage (:conc-name usage-))
  (operations (make-hash-table :test #'eq))
  (slots (make-hash-table :test #'equal))
  (computed (make-hash-table :test #'eq))
  (flags (make-hash-table :test #'eq)))

(defun usage-mark-operation (usage operation)
  (setf (gethash operation (usage-operations usage)) t))

(defun usage-need-slot (usage operation slot)
  "Record that SLOT's OPERATION helper must exist, without implying a use."
  (when (eq operation :write) (usage-need-slot usage :read slot))
  ;; Every reader signals the shared unbound-slot slow path.
  (when (eq operation :read) (usage-mark-operation usage :unbound))
  (setf (gethash (cons operation slot) (usage-slots usage)) t))

(defun usage-mark-slot (usage operation slot)
  (usage-mark-operation usage operation)
  (usage-need-slot usage operation slot))

(defun usage-mark-computed (usage operation)
  (when (eq operation :write)
    (usage-mark-operation usage :read)
    (setf (gethash :read (usage-computed usage)) t))
  (when (eq operation :read) (usage-mark-operation usage :unbound))
  (usage-mark-operation usage operation)
  (setf (gethash operation (usage-computed usage)) t))

(defun usage-need-every-slot (usage operation)
  (usage-mark-operation usage operation)
  (setf (gethash operation (usage-computed usage)) t))

(defun usage-mark-flag (usage name)
  (setf (gethash name (usage-flags usage)) t))

(defun usage-operation-p (usage operation)
  (gethash operation (usage-operations usage)))

(defun usage-computed-p (usage operation)
  (gethash operation (usage-computed usage)))

(defun usage-slot-p (usage operation slot)
  (gethash (cons operation slot) (usage-slots usage)))

(defun usage-flag-p (usage name)
  (gethash name (usage-flags usage)))

(defun scan-usage-list (build usage forms)
  (mapc (lambda (form) (scan-usage-form build usage form)) forms))

(defun scan-slot-operand (build usage operation operand)
  (if (and (quoted operand) (symbolp (second operand))
           (known-record-slot-p build (second operand)))
      (usage-mark-slot usage operation (second operand))
      (usage-mark-computed usage operation)))

(defun scan-usage-form (build usage form)
  (when (consp form)
    (let ((operator (first form)))
      (cond
        ((eq operator 'quote)
         ;; A quoted designator can still reach the general path.
         (when (member (second form) '(equalp make-instance)) (usage-mark-flag usage (second form)))
         (when (metadata-operation-name (second form)) (usage-mark-flag usage (second form))))
        ((and (eq operator 'function) (function-name-p (second form)))
         (let ((target (second form)))
           (if (member target '(equalp make-instance))
               (usage-mark-flag usage target)
               (when (metadata-operation-name target) (usage-mark-flag usage target)))))
        ((eq operator 'setf)
         (loop for (place value) on (rest form) by #'cddr
               do (if (and (consp place) (eq (first place) 'slot-value))
                      (progn (scan-slot-operand build usage :write (third place))
                             (scan-usage-list build usage (rest place)))
                      (scan-usage-form build usage place))
                  (scan-usage-form build usage value)))
        ((member operator '(slot-value slot-boundp slot-makunbound))
         (scan-slot-operand build usage (ecase operator (slot-value :read) (slot-boundp :boundp)
                                                     (slot-makunbound :unbind))
                            (third form))
         (scan-usage-list build usage (rest form)))
        ((eq operator 'make-instance)
         ;; A literal owned class reaches its constructor without the class table.
         (unless (literal-record-class-p build (second form)) (usage-mark-flag usage 'make-instance))
         (scan-usage-list build usage (rest form)))
        ((metadata-operation-name operator)
         (usage-mark-flag usage operator)
         (scan-usage-list build usage (rest form)))
        (t
         (when (eq operator 'equalp) (usage-mark-flag usage 'equalp))
         (scan-usage-list build usage form))))))

(defun literal-record-class-p (build form)
  (and (quoted form) (symbolp (second form)) (find-record-class build (second form))))

(defun scan-class-accessors (build usage)
  (dolist (form (build-forms build))
    (when (eq (first form) 'defclass)
      (dolist (slot (fourth form))
        (when (consp slot)
          (let ((name (first slot)))
            (loop for (key value) on (rest slot) by #'cddr
                  do (case key
                       (:reader (usage-mark-slot usage :read name))
                       (:accessor (usage-mark-slot usage :read name)
                                  (usage-mark-slot usage :write name))
                       (:writer (usage-mark-slot usage :write name))
                       (:initform (scan-usage-form build usage value))))))))))

(defun scan-class-defaults (build usage)
  (dolist (form (build-forms build))
    (when (eq (first form) 'defclass)
      (let ((option (assoc :default-initargs (cddddr form))))
        (when option
          (loop for (key value) on (rest option) by #'cddr
                do (scan-usage-form build usage value)))))))

(defun scan-constructor-writes (build usage)
  ;; A constructor stores every supplied or defaulted slot through its writer.
  (dolist (description (build-layouts build))
    (dolist (slot (class-description-slots description))
      (when (or (slot-description-initargs slot) (slot-description-initform-p slot))
        (usage-need-slot usage :write (slot-description-name slot))))))

(defun scan-read-writers (build usage)
  ;; The UNBOUND-SLOT store-value restart writes through the reader's own slot.
  (if (usage-computed-p usage :read)
      (usage-need-every-slot usage :write)
      (dolist (description (build-layouts build))
        (dolist (slot (class-description-slots description))
          (let ((name (slot-description-name slot)))
            (when (usage-slot-p usage :read name)
              (usage-mark-slot usage :write name)))))))

(defun scan-usage (build)
  "Index the retained helper surface reachable from the normalized source."
  (let ((usage (make-usage)))
    (dolist (form (build-forms build)) (scan-usage-form build usage form))
    (scan-class-accessors build usage)
    (scan-class-defaults build usage)
    (scan-constructor-writes build usage)
    (scan-read-writers build usage)
    (setf (build-usage build) usage)))

(defun usage-needs-metadata-p (usage)
  "The logical class table is the only route to a non-literal class operand."
  (or (usage-flag-p usage 'make-instance)
      ;; EQUALP distinguishes logical classes from native structures.
      (usage-flag-p usage 'equalp)
      (loop for flag being the hash-keys of (usage-flags usage)
            thereis (metadata-operation-name flag))))

(defun usage-slot-operations (build usage operation)
  "Slot names needing an emitted helper for OPERATION."
  (let ((slots (remove-duplicates
                (loop for description in (build-layouts build)
                      append (mapcar #'slot-description-name (class-description-slots description))))))
    (if (usage-computed-p usage operation)
        slots
        (remove-if-not (lambda (slot) (usage-slot-p usage operation slot)) slots))))

(defun usage-symbol-dispatch-p (usage operation)
  "Whether a runtime slot-name entry point is reachable for OPERATION."
  (or (usage-computed-p usage operation)
      ;; %RECORD-UNBOUND's store-value restart calls the read dispatcher, and
      ;; that dispatcher writes through (setf %RECORD-READ). Both dispatchers
      ;; must exist whenever an unbound read is reachable.
      (and (member operation '(:read :write))
           (usage-operation-p usage :read))))
