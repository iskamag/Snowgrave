;;;; Hosted predicate cost only; not whole dispatch or native admission.
(require :asdf)
(let ((root (uiop:pathname-parent-directory-pathname
             (uiop:pathname-directory-pathname *load-truename*))))
  (asdf:initialize-source-registry
   `(:source-registry (:directory ,root) :ignore-inherited-configuration))
  (asdf:initialize-output-translations
   `(:output-translations (t ,(merge-pathnames ".build/layout-cost-fasl/" root))
     :ignore-inherited-configuration)))
(asdf:load-system "snowgrave")

(defun measure-layout-predicate (function count)
  (assert (= 1000 (funcall function 1000)))
  (let ((samples nil))
    (dotimes (sample 3)
      (let ((start (get-internal-real-time)))
        (assert (= count (funcall function count)))
        (push (* 1d9 (/ (- (get-internal-real-time) start)
                       internal-time-units-per-second count)) samples)))
    (second (sort samples #'<))))

(dolist (width '(1 16 128 1024))
  (let* ((class 'measured-layout)
         (identity (list 'layout-predicate-cost :slots width))
         (slots (loop for index below width collect (intern (format nil "SLOT-~D" index))))
         (ancestors (list class))
         (types (make-list width :initial-element t))
         (layout (snowgrave:make-layout identity class ancestors slots :slot-types types))
         (record (snowgrave:sg-make-record layout))
         (detailed (lambda (count)
                     (loop repeat count count
                       (snowgrave:sg-record-layout-p record identity class ancestors slots
                                                    :slot-types types :error-mapping nil))))
         (admitted (lambda (count)
                     (loop repeat count count (snowgrave:sg-record-matches-layout-p record layout)))))
    (format t "slots=~D detailed=~,2F ns admitted=~,2F ns (median of 3 hosted samples)~%"
            width (measure-layout-predicate detailed 300000)
            (measure-layout-predicate admitted 300000))))
(format t "Each admitted row guard is independent of schema width; cell selection, field access and target checks are separate costs.~%")
