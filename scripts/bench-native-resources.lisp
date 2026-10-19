;;;; Cold named-resource indexing benchmark, with input/manifest setup excluded.
;;;; Run: sbcl --script scripts/bench-native-resources.lisp [resource-count ...]
;;;; No hot collector or target performance claim.
(require :asdf)
(let* ((root (truename (merge-pathnames "../" (uiop:pathname-directory-pathname *load-truename*))))
       (cache (merge-pathnames "snowgrave-resource-scaling/" (uiop:temporary-directory))))
  (asdf:initialize-source-registry `(:source-registry (:directory ,root) :ignore-inherited-configuration))
  (asdf:initialize-output-translations `(:output-translations (t ,cache) :ignore-inherited-configuration)))
(asdf:load-system "snowgrave")
(defun resource-scaling-input (count)
  (values (loop for id below count collect (list id (make-array 0)))
          (list :resources (loop for id below count collect (list :key id :node id))
                :nodes (loop for id below count collect
                         (list :id id :path (list :resource id) :kind :array
                               :dimensions '(0) :element-type t :adjustable nil
                               :has-fill-pointer nil :backing nil :offset 0 :links nil)))))
(defun resource-scaling-trial (bindings manifest)
  (sb-ext:gc :full t)
  (let ((start (get-internal-real-time)) (bytes (sb-ext:get-bytes-consed)))
    (snowgrave:with-native-bindings ('(:resource-scaling) bindings)
      (let ((roots (snowgrave::%resolve-native-bindings '(:resource-scaling) manifest)))
        (assert (= (length bindings) (length roots)))
        (loop for binding in bindings for root across roots do (assert (eq (second binding) root)))))
    (list (- (sb-ext:get-bytes-consed) bytes)
          (/ (- (get-internal-real-time) start) (float internal-time-units-per-second)))))
(multiple-value-bind (bindings manifest) (resource-scaling-input 32)
  (resource-scaling-trial bindings manifest))
(format t "~&Hosted cold resource indexing on ~A ~A; three trials, no timing thresholds.~%"
        (lisp-implementation-type) (lisp-implementation-version))
(dolist (count (or (mapcar #'parse-integer (uiop:command-line-arguments)) '(512 2048 8192 16384)))
  (multiple-value-bind (bindings manifest) (resource-scaling-input count)
    (let* ((trials (loop repeat 3 collect (resource-scaling-trial bindings manifest)))
           (bytes (sort (mapcar #'first trials) #'<))
           (seconds (sort (mapcar #'second trials) #'<)))
      (format t "RESOURCE-SCALING count=~D median-bytes=~D median-seconds=~,6F~%"
              count (second bytes) (second seconds)))))
