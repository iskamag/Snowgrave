;;;; Hosted cold capture/installation costs, with input arrays preallocated.
;;;; Run: sbcl --script scripts/bench-configuration-imports.lisp [cell-count ...]
(require :asdf)
(let* ((root (truename (merge-pathnames "../" (uiop:pathname-directory-pathname *load-truename*))))
       (cache (merge-pathnames (format nil "snowgrave-import-bench-~D/" (sxhash (namestring root)))
                              (uiop:temporary-directory))))
  (asdf:initialize-source-registry `(:source-registry (:directory ,root) :ignore-inherited-configuration))
  (asdf:initialize-output-translations `(:output-translations (t ,cache) :ignore-inherited-configuration)))
(asdf:load-system "snowgrave/sbcl")
(defpackage #:snowgrave.configuration-import-benchmark (:use #:cl))
(in-package #:snowgrave.configuration-import-benchmark)

(defvar *sequence* 0)
(defvar *retained-input-and-build* nil)
(defun identity-key () (list :configuration-import-benchmark (incf *sequence*)))
(defun forms () '((defun entry (data) (length data))))
(defun input-array (size type value) (make-array size :element-type type :initial-element value))
(defun seconds-since (time)
  (/ (- (get-internal-real-time) time) (float internal-time-units-per-second 1d0)))
(defun report (operation kind size type bytes seconds &optional retained)
  (format t "~&~A ~S cells=~D type=~S allocated=~D seconds=~,6F~@[ retained=~D~]~%"
          operation kind size type bytes seconds retained))

(defun owner-sample (kind size type value)
  ;; Input/build allocation precedes measurement. Retained bytes are a coarse
  ;; post-full-GC dynamic-space delta, with the resulting build kept live.
  (let* ((data (input-array size type value))
         (key (identity-key))
         (output (unless (eq kind :scan)
                   (make-package (symbol-name (gensym "IMPORT-BENCH.")) :use '(:cl))))
         (build (when output
                  (snowgrave.sbcl::make-build
                   :identity key :source (snowgrave:make-authored-source (forms) :identity key)
                   :output-package output
                   :declaration (list :entries '(entry)
                                      :external-domains (list (list 'entry (list (list 'eql data))))
                                      :native-bindings (when (eq kind :import) (list (list :data data)))))))
         (invalid 0))
    (setf *retained-input-and-build* (list data build))
    (unwind-protect
         (progn
           (sb-ext:gc :full t)
           (let ((live (sb-kernel:dynamic-usage)) (before (sb-ext:get-bytes-consed))
                 (time (get-internal-real-time)))
             (if build (snowgrave.sbcl::capture-entry-graph build)
                 (dotimes (i size) (unless (numberp (aref data i)) (incf invalid))))
             (let ((bytes (- (sb-ext:get-bytes-consed) before)) (elapsed (seconds-since time)))
               (sb-ext:gc :full t)
               (report :capture kind size type bytes elapsed (- (sb-kernel:dynamic-usage) live))))
           (assert (zerop invalid))
           (when (eq kind :import)
             (let ((manifest (snowgrave.sbcl::graph-native-manifest build)))
               (sb-ext:gc :full t)
               (let ((before (sb-ext:get-bytes-consed)) (time (get-internal-real-time)))
                 (snowgrave:with-native-bindings (key (list (list :data data)))
                   (assert (eq data (aref (snowgrave::%resolve-native-bindings key manifest) 0))))
                 (report :resolve kind size type (- (sb-ext:get-bytes-consed) before) (seconds-since time))))))
      (when output (snowgrave.sbcl::clean-package output))
      (setf *retained-input-and-build* nil))))

(defun public-sample (size type value &key distinct-scalars)
  ;; Public close includes source ownership, compiler passes, import validation,
  ;; semantic/residual audits and installation. It is not the capture-only cost.
  (let ((data (input-array size type value)) (key (identity-key)))
    (when distinct-scalars
      (dotimes (index size) (setf (aref data index) (+ value index))))
    (sb-ext:gc :full t)
    (let* ((before (sb-ext:get-bytes-consed)) (time (get-internal-real-time))
           (unit (snowgrave:close-source-unit
                  (list :forms (forms)) :unit-name key :entries '(entry) :universe '(vector integer)
                  :external-domains (list (list 'entry (list (list 'eql data))))
                  :native-bindings (list (list :data data))))
           (bytes (- (sb-ext:get-bytes-consed) before)) (elapsed (seconds-since time)))
      (assert (= size (funcall (snowgrave:unit-function unit 'entry :bind-configuration t))))
      (unless (zerop size)
        (assert (and (eql value (aref data 0))
                     (eql (if distinct-scalars (+ value (1- size)) value) (aref data (1- size))))))
      (report :close (if distinct-scalars :import-distinct-scalars :import) size type bytes elapsed))))

(format t "~&Hosted cold costs on ~A ~A; seconds are coarse samples, no thresholds.~%"
        (lisp-implementation-type) (lisp-implementation-version))
;; Warm compilation/capture paths, then compare zero-size overhead and growth.
(owner-sample :import 16 t 17)
(public-sample 16 t 17)
(dolist (size (or (mapcar #'parse-integer (uiop:command-line-arguments)) '(0 65536 1048576)))
  (owner-sample :scan size t 17)
  (owner-sample :owned size t 17)
  (owner-sample :import size t 17)
  (owner-sample :import size '(unsigned-byte 64) (1- (ash 1 64)))
  (public-sample size t 17)
  (public-sample size '(unsigned-byte 64) (1- (ash 1 64)))
  (public-sample size t (ash 1 64) :distinct-scalars t))
