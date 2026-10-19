(in-package #:snowgrave.tests)

(defvar *physical-type-sequence* 0)

(defun physical-type-case (tag definitions body &key refusal (configured t) (policy :entries)
                                                   (expected '(17)) fresh (inventory-kind :vector) data-root native-error)
  (let* ((index (incf *physical-type-sequence*))
         (package (make-package (format nil "SNOWGRAVE.PHYSICAL.TYPE.~D" index) :use '("CL")))
         (forms (let ((*package* package))
                  (read-from-string
                   (format nil "((defclass holder () ((data :initarg :data) (inventory :initarg :inventory)))
                                  (defgeneric operation ()) (defmethod operation () 17)
                                  ~A
                                  (defun boot () (make-instance 'holder :data 17 :inventory nil))
                                  (defun entry (object) (declare (ignorable object)) ~A))" definitions body))))
         (holder (intern "HOLDER" package)) (entry (intern "ENTRY" package))
         (boot (intern "BOOT" package)) (root (progn (dolist (form forms) (eval form))
                                                     (make-instance holder :data 17)))
         (unit nil) (condition nil))
    (setf (slot-value root (intern "INVENTORY" package))
          (ecase inventory-kind (:vector (vector root)) (:cons (list root))))
    (when data-root (setf (slot-value root (intern "DATA" package)) root))
    ;; These negative declarations are valid in the source program. Their
    ;; failure is introduced by lowering, rather than a source type mistake.
    (let ((native-root (make-instance holder :data 17)))
      (setf (slot-value native-root (intern "INVENTORY" package))
            (ecase inventory-kind (:vector (vector native-root)) (:cons (list native-root))))
      (when data-root (setf (slot-value native-root (intern "DATA" package)) native-root))
      (if native-error
          (check (handler-case (progn (funcall entry native-root) nil) (type-error () t)))
          (check (equal expected (multiple-value-list (funcall entry native-root))))))
    (setf unit
          (handler-case
              (snowgrave:close-source-unit
               (list :forms forms) :unit-name (list :physical-type-input tag index)
               :closed-classes (list holder) :closed-generics (list (intern "OPERATION" package))
               :universe (list holder 'number 'symbol 'list 'cons 'vector t)
               :entries (if configured (list entry) (list boot entry)) :deployment-roots policy
               :external-domains (if configured (list (list entry (list (list 'eql root))))
                                     (list (list boot nil) (list entry (list holder)))))
            (snowgrave:snowgrave-error (error) (setf condition error) nil)))
    (if refusal
        (progn (check (typep condition 'snowgrave:snowgrave-error))
               (unless (eq refusal (snowgrave:error-feature condition))
                 (error "~S expected ~S, got ~A" tag refusal condition))
               (check (eq refusal (snowgrave:error-feature condition))))
        (progn
          (when condition (error "Unexpected ~S refusal: ~A" tag condition))
          (check unit)
          (check (equal expected
                        (multiple-value-list
                         (if configured
                             (funcall (snowgrave:unit-function unit entry :bind-configuration t))
                             (funcall (snowgrave:unit-function unit entry)
                                      (funcall (snowgrave:unit-function unit boot)))))))
          (when fresh (physical-type-fresh-test unit))))))

(defun physical-type-input-tests ()
  (let ((gf "(defun run (callback)
               (declare (type (and function (not compiled-function)) callback)) (funcall callback))")
        (record "(defun run (object)
                   (declare (type (not structure-object) object)) (slot-value object 'data))"))
    (dolist (policy '(:entries :selected))
      (physical-type-case (list :gf policy) gf "(run #'operation)" :policy policy
                          :refusal :private-type-declaration-error)
      (physical-type-case (list :record policy) record "(run object)" :policy policy
                          :refusal :private-type-declaration-error))
    (physical-type-case :ordinary-gf gf "(run #'operation)" :configured nil
                        :refusal :private-type-declaration-error)
    (physical-type-case :ordinary-record record "(run object)" :configured nil
                        :refusal :private-type-declaration-error))
  (physical-type-case :shorthand "(defun run (callback)
                                    (declare ((and function (not compiled-function)) callback))
                                    (funcall callback))" "(run #'operation)"
                      :refusal :private-type-declaration-error)
  (physical-type-case :alias-default "(defun run (&optional (callback #'operation))
                                       (let ((saved callback))
                                         (declare (type (not compiled-function) saved))
                                         (funcall saved)))" "(run)"
                      :refusal :private-type-declaration-error)
  (physical-type-case :assignment "(defun run (first second)
                                    (let ((saved first))
                                      (declare (type (not structure-object) saved))
                                      (setq saved second) (slot-value saved 'data)))"
                      "(run object object)" :refusal :private-type-declaration-error)
  (physical-type-case :joined-record "(defun run (value)
                                       (declare (type (not structure-object) value))
                                       (if (numberp value) value 17))"
                      "(run 17) (run object)" :refusal :private-type-declaration-error)
  (physical-type-case :safe-function "(defun run (callback)
                                       (declare (type function callback)) (funcall callback))"
                      "(run #'operation)" :fresh t)
  (physical-type-case :safe-record-t "(defun run (object)
                                       (declare (type t object)) (slot-value (the t object) 'data))"
                      "(run object)" :fresh t)
  (physical-type-case :safe-function-alias "(defun run (&optional (callback #'operation))
                                            (let ((saved callback))
                                              (declare (type function saved))
                                              (funcall saved)))" "(run)")
  (physical-type-case :native-function "(defun run (callback)
                                         (declare (type compiled-function callback))
                                         (funcall callback '(17)) 17)" "(run #'car)")
  (physical-type-case :private-vector "(defun run (inventory)
                                        (declare (type (simple-vector 1) inventory))
                                        (vectorp inventory) 17)"
                      "(run (slot-value object 'inventory))")
  (physical-type-case :private-cons "(defun run (inventory)
                                      (declare (type cons inventory))
                                      (consp (the list inventory)) 17)"
                      "(run (slot-value object 'inventory))" :inventory-kind :cons)
  (physical-type-case :joined-native-container "(defun run (value)
                                                (declare (type (or integer vector) value)) 17)"
                      "(run 17) (run (slot-value object 'inventory))")
  (physical-type-case :ordinary-safe-record "(defun run (object)
                                             (declare (type t object)) (slot-value (the t object) 'data))"
                      "(run object)" :configured nil)
  (physical-type-case :the-error "" "(the cons object) 17" :native-error t
                      :refusal :private-type-assertion-error)
  (physical-type-case :the-saved-value ""
                      "(the list (prog1 (slot-value object 'data)
                                   (setf (slot-value object 'data) nil))) 17"
                      :data-root t :native-error t :refusal :private-type-assertion-error)
  (physical-type-case :the-earlier-effect ""
                      "(the list (progn (setf (slot-value object 'data) nil)
                                    (setf (slot-value object 'data) object)
                                    (slot-value object 'data))) 17"
                      :native-error t :refusal :private-type-assertion-error)
  (physical-type-case :native-number "(defun run (value)
                                       (declare (type integer value)) (the integer value))" "(run 17)"))

(defun physical-type-fresh-test (unit)
  (let ((root (asdf:system-source-directory "snowgrave"))
        (cache (merge-pathnames "snowgrave-physical-type-fresh/" (uiop:temporary-directory))))
    (uiop:with-temporary-file (:pathname source :stream source-stream :type "lisp")
      (snowgrave:write-unit-source unit source-stream) (finish-output source-stream)
      (uiop:with-temporary-file (:pathname metadata :stream metadata-stream :type "metadata")
        (snowgrave:write-unit-metadata unit metadata-stream) (finish-output metadata-stream)
        (uiop:with-temporary-file (:pathname driver :stream driver-stream :type "lisp")
          (let ((fasl (compile-file-pathname source)))
            (unwind-protect
                 (progn
                   (dolist (form
                            `((require :asdf)
                              (make-package "SNOWGRAVE.TESTS" :use '("CL"))
                              (asdf:initialize-source-registry
                               '(:source-registry (:directory ,root) :ignore-inherited-configuration))
                              (asdf:initialize-output-translations
                               '(:output-translations (t ,cache) :ignore-inherited-configuration))
                              (asdf:load-system "snowgrave")
                              (multiple-value-bind (artifact warnings failure) (compile-file ,source :output-file ,fasl)
                                (declare (ignore warnings)) (assert (not failure))
                                (let* ((data (with-open-file (in ,metadata) (read in)))
                                       (entry (find "ENTRY" (getf data :entries) :test #'string=
                                                    :key (lambda (row) (symbol-name (getf row :name)))))
                                       (key (getf entry :bound-code-key)))
                                  (assert (not (find-class (find-symbol "HOLDER" (symbol-package (getf entry :name))) nil)))
                                  (assert (not (fboundp (find-symbol "OPERATION" (symbol-package (getf entry :name))))))
                                  (load (if (uiop:command-line-arguments) artifact ,source))
                                  (assert (equal '(17) (multiple-value-list
                                                       (funcall (fdefinition (find-symbol (second key) (first key)))))))))
                              (assert (not (let ((package (find-package "SNOWGRAVE.SBCL")))
                                             (and package (fboundp (find-symbol "CLOSE-SOURCE" package))))))
                              (format t "Fresh physical type checked.~%")))
                     (write form :stream driver-stream :readably t) (terpri driver-stream))
                   (finish-output driver-stream)
                   (dolist (mode '(nil "fasl"))
                     (check (search "Fresh physical type checked."
                                    (uiop:run-program
                                     (append (list "sbcl" "--no-sysinit" "--no-userinit" "--script" (namestring driver))
                                             (when mode (list mode)))
                                     :output :string :error-output *error-output*)))))
              (when (probe-file fasl) (delete-file fasl)))))))))
