(in-package #:snowgrave)

(defvar *native-binding-contexts* nil)

(defun binding-key-p (value)
  "Stable scalar/list keys, with no instance printing or process identities."
  (let ((seen (make-hash-table :test #'eq)))
    (labels ((walk (part)
               (cond ((symbolp part) (not (null (symbol-package part))))
                     ((or (numberp part) (characterp part) (stringp part)) t)
                     ((consp part)
                      (case (gethash part seen)
                        (:complete t) (:active nil)
                        (otherwise
                         (setf (gethash part seen) :active)
                         (when (and (walk (car part)) (walk (cdr part)))
                           (setf (gethash part seen) :complete) t))))
                     (t nil))))
      (walk value))))

(defun native-binding-error (identity feature detail)
  (reject 'unsupported-definition :installation feature detail :path (list identity)))

(defun call-with-native-bindings (identity bindings function)
  (unless (and (binding-key-p identity) (source-finite-list-p bindings))
    (native-binding-error identity :native-binding-context
                          "A resource context needs a stable unit key and finite binding list."))
  (let ((owned nil))
    (dolist (binding bindings)
      (unless (and (source-finite-list-p binding) (= (length binding) 2)
                   (binding-key-p (first binding)) (arrayp (second binding))
                   (not (assoc (first binding) owned :test #'equal)))
        (native-binding-error identity :native-binding-context
                              "Each native resource needs one unique stable key and an actual array."))
      (push (list (immutable-copy (first binding)) (second binding)) owned))
    (let ((*native-binding-contexts*
            (acons (immutable-copy identity) (nreverse owned) *native-binding-contexts*)))
      (funcall function))))

(defmacro with-native-bindings ((identity bindings) &body body)
  "Supply cold native resources while installing an artifact of IDENTITY.
Installation checks its manifest before publication. The installed graph keeps
the resources alive after this scope; ending the scope releases no authority."
  `(call-with-native-bindings ,identity ,bindings (lambda () ,@body)))

(defun native-binding-path (identity path bindings)
  (unless (and (source-finite-list-p path) (eq (first path) :resource) (cdr path))
    (native-binding-error identity :native-binding-path "A native path starts at a named resource."))
  (let ((binding (assoc (second path) bindings :test #'equal)))
    (unless binding
      (native-binding-error identity :native-binding-missing "A required native resource has no binding."))
    (let ((value (second binding)))
      (dolist (step (cddr path) value)
        (unless (and (source-finite-list-p step) step)
          (native-binding-error identity :native-binding-path "A native path has an invalid step."))
        (setf value
              (case (first step)
                (:element
                 (unless (and (= (length step) 2) (arrayp value) (array-element-type value)
                              (integerp (second step)) (<= 0 (second step))
                              (< (second step) (array-total-size value)))
                   (native-binding-error identity :native-binding-path "A native element path is out of bounds."))
                 (row-major-aref value (second step)))
                ((:car :cdr)
                 (unless (and (= (length step) 1) (consp value))
                   (native-binding-error identity :native-binding-path "A native list path needs a cons."))
                 (if (eq (first step) :car) (car value) (cdr value)))
                (:backing
                 (unless (and (= (length step) 1) (arrayp value) (array-displacement value))
                   (native-binding-error identity :native-binding-path "A native backing path needs a displaced array."))
                 (array-displacement value))
                (otherwise
                 (native-binding-error identity :native-binding-path "An unsupported native path step was supplied."))))))))

(defun %resolve-native-bindings (identity manifest)
  "Resolve the complete cold manifest before any configuration is callable."
  (let* ((context (assoc identity *native-binding-contexts* :test #'equal))
         (bindings (cdr context)) (resources (getf manifest :resources))
         (nodes (getf manifest :nodes))
         (by-id (make-hash-table :test #'eql)) (by-value (make-hash-table :test #'eq)))
    (unless (and context (= (length bindings) (length resources))
                 (every (lambda (resource) (assoc (getf resource :key) bindings :test #'equal)) resources))
      (native-binding-error identity :native-binding-missing
                            "The native binding context must match the complete resource manifest."))
    (dolist (node nodes)
      (let* ((id (getf node :id))
             (value (native-binding-path identity (getf node :path) bindings)))
        (unless (and (integerp id) (<= 0 id) (not (nth-value 1 (gethash id by-id))))
          (native-binding-error identity :native-binding-manifest "Each manifest node has a unique finite identity."))
        (when (nth-value 1 (gethash value by-value))
          (native-binding-error identity :native-binding-alias "Distinct native nodes cannot collapse to one binding."))
        (unless (case (getf node :kind)
                  (:cons (consp value))
                  (:array
                   (and (arrayp value) (equal (array-dimensions value) (getf node :dimensions))
                        (equal (array-element-type value) (getf node :element-type))
                        (eq (not (null (adjustable-array-p value))) (not (null (getf node :adjustable))))
                        (eq (not (null (array-has-fill-pointer-p value)))
                            (not (null (getf node :has-fill-pointer))))
                        (or (not (array-has-fill-pointer-p value))
                            (eql (fill-pointer value) (getf node :fill-pointer)))))
                  (otherwise nil))
          (native-binding-error identity :native-binding-geometry "A bound native node does not match its admitted geometry."))
        (setf (gethash id by-id) value (gethash value by-value) id)))
    (dolist (node nodes)
      (let ((value (gethash (getf node :id) by-id))
            (links (make-hash-table :test #'eql)))
        ;; Index once: a dense native vector must not scan all links for each
        ;; physical cell. This table exists only during cold installation.
        (dolist (link (getf node :links))
          (let ((step (first link)))
            (unless (and (source-finite-list-p link) (= (length link) 2)
                         (if (eq (getf node :kind) :cons)
                             (member step '(:car :cdr))
                             (and (integerp step) (<= 0 step) (< step (array-total-size value))))
                         (not (nth-value 1 (gethash step links)))
                         (nth-value 1 (gethash (second link) by-id)))
              (native-binding-error identity :native-binding-manifest
                                    "A native link needs one valid edge and admitted target."))
            (setf (gethash step links) (second link))))
        (flet ((check-edge (step element)
                 (multiple-value-bind (target linkedp) (gethash step links)
                   (unless (if linkedp
                               (eq element (gethash target by-id))
                               (or (numberp element) (characterp element)
                                   (and (symbolp element) (symbol-package element))))
                     (native-binding-error identity :native-binding-alias
                                           "A native data edge changed its admitted identity relation.")))))
          (case (getf node :kind)
            (:cons (check-edge :car (car value)) (check-edge :cdr (cdr value)))
            (:array
             (multiple-value-bind (backing offset) (array-displacement value)
               (let ((parent-id (getf node :backing)))
                 (unless (and (if parent-id
                                  (and (nth-value 1 (gethash parent-id by-id))
                                       (eq backing (gethash parent-id by-id)))
                                  (null backing))
                              (= offset (getf node :offset 0)))
                   (native-binding-error identity :native-binding-alias "A native displacement relation changed.")))
               (unless (or backing (null (array-element-type value)))
                 (dotimes (index (array-total-size value))
                   (check-edge index (row-major-aref value index))))))))))
    (map 'vector
         (lambda (resource)
           (let ((value (second (assoc (getf resource :key) bindings :test #'equal))))
             (unless (and (nth-value 1 (gethash (getf resource :node) by-id))
                          (eq value (gethash (getf resource :node) by-id)))
               (native-binding-error identity :native-binding-alias "A native root no longer names its admitted node."))
             value)) resources)))

