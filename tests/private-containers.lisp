(in-package #:snowgrave.tests)

(defvar *private-container-sequence* 0)
(defvar *private-container-events* nil)
(defun private-container-note (value) (push value *private-container-events*) nil)
(defun private-container-choice () nil)

(defun private-container-observation (function backing)
  (let ((*private-container-events* nil))
    (handler-case
        (let ((values (multiple-value-list (catch :outside (funcall function)))))
          (list :values values :events (reverse *private-container-events*) :backing (coerce backing 'list)))
      (error (condition)
        (list :error (type-of condition) :events (reverse *private-container-events*)
              :backing (coerce backing 'list))))))

(defun private-container-control (tag body &key refuse (kind :vector) extra fresh import-inventory)
  (let* ((package (make-package (format nil "SNOWGRAVE.PRIVATE-CONTAINERS.~D" (incf *private-container-sequence*))
                                :use '("CL")))
         (forms (let ((*package* package))
                  (append (read-from-string
                           "((defclass leaf () ())
                             (defclass anchor () ((data :initarg :data :reader backing)
                                                  (inventory :initarg :inventory) (other :initarg :other)))
                             (defgeneric clear (root))
                             (defmethod clear ((root anchor)) (fill (backing root) nil) 17)
                             (defun keep (value) value)
                             (defun ignore-inventory (value) (declare (ignore value)) 17))")
                          (when extra (read-from-string extra))
                          (read-from-string (format nil "((defun entry (root) (clear root) ~A))" body)))))
         (entry (intern "ENTRY" package)) (inventory-slot (intern "INVENTORY" package)))
    (dolist (form forms) (eval form))
    (labels ((graph ()
               (let* ((data (vector 17 23)) (root (make-instance (intern "ANCHOR" package) :data data))
                      (leaf (make-instance (intern "LEAF" package)))
                      (other (make-instance (intern "LEAF" package)))
                      (inventory
                        (ecase kind
                          (:vector (vector (cons leaf nil) root leaf))
                          (:list (list leaf root leaf))
                          (:displaced
                           (let ((backing (make-array 4 :initial-element nil)))
                             (setf (aref backing 3) root)
                             (make-array 2 :displaced-to backing))))))
                 (setf (slot-value root inventory-slot) inventory
                       (slot-value root (intern "OTHER" package)) (vector (cons other nil) root other))
                 (values root data inventory))))
      (multiple-value-bind (native-root native-backing) (graph)
        (multiple-value-bind (root backing inventory) (graph)
          (let* ((native (private-container-observation (lambda () (funcall entry native-root)) native-backing))
                 (*private-container-events* nil)
                 (condition nil)
                 (unit (handler-case
                           (snowgrave:close-source-unit
                            (list :forms forms) :unit-name (list :private-container tag *private-container-sequence*)
                            :closed-classes (loop for form in forms when (eq (first form) 'defclass) collect (second form))
                            :closed-generics (list (intern "CLEAR" package) (intern "BACKING" package))
                            :universe (append (loop for form in forms when (eq (first form) 'defclass) collect (second form))
                                              '(integer number symbol cons list vector t))
                            :entries (list entry) :external-domains (list (list entry (list (list 'eql root))))
                            :native-bindings (append (list (list :backing backing))
                                                     (when import-inventory (list (list :inventory inventory))))
                            :external-operations '(private-container-note private-container-choice))
                         (snowgrave:snowgrave-error (c) (setf condition c) nil))))
            (check (null *private-container-events*))
            (if refuse
                (progn
                  (check (typep condition 'snowgrave:snowgrave-error))
                  ;; The failure must be in the actual entry, rather than an
                  ;; unrelated retained CLEAR body lacking its real caller.
                  (check (equal (list (list :private-container tag *private-container-sequence*) (length forms))
                                (snowgrave:error-source-key condition))))
                (progn
                  (when condition (error "Unexpected ~S refusal: ~A" tag condition))
                  (check (null condition))
                  (check (equal native (private-container-observation
                                        (snowgrave:unit-function unit entry :bind-configuration t) backing)))
                  (check (every #'null backing))
                  (when fresh (private-container-fresh-test unit))))))))))

(defun private-container-tests ()
  (private-container-control :clear
   "(values (vectorp (slot-value root 'inventory))
            (eq (keep (slot-value root 'inventory)) (slot-value root 'inventory))
            (eq root root) (clear root))" :fresh t)
  (private-container-control :ignored-internal-input
   "(ignore-inventory (slot-value root 'inventory))")
  (private-container-control :internal-slot-acceptance
   "(setf (slot-value root 'other) (slot-value root 'inventory))
    (vectorp (slot-value root 'other))")
  (dolist (kind '(:list :displaced))
    (private-container-control (list :unused kind) "(clear root)" :kind kind))
  (dolist (body '("(slot-value root 'inventory)"
                  "(values 17 (slot-value root 'inventory))"
                  "(list (slot-value root 'inventory))"
                  "(throw :outside (slot-value root 'inventory))"
                  "(error \"inventory ~S\" (slot-value root 'inventory))"
                  "(snowgrave.tests::private-container-note (keep (slot-value root 'inventory))) 17"
                  "(fill (slot-value root 'inventory) nil :start 8) 17"
                  "(find t (slot-value root 'inventory) :key
                         (lambda (item) (snowgrave.tests::private-container-note item) t)) 17"
                  "(snowgrave.tests::private-container-note (aref (slot-value root 'inventory) 1)) 17"
                  "(let ((alias (slot-value root 'data)))
                     (setf (aref alias 0) (slot-value root 'inventory))) 17"
                  "(let ((value (if (snowgrave.tests::private-container-choice)
                                   (vector 0) (slot-value root 'inventory))))
                     (when (vectorp value) (fill value nil :start 8))) 17"
                  "(let ((value (slot-value root 'inventory)))
                     (setf value (if (snowgrave.tests::private-container-choice) (vector 0) value))
                     (when (vectorp value) (fill value nil :start 8))) 17"
                  "(the list (slot-value root 'inventory))"
                  "(equalp (slot-value root 'inventory) (slot-value root 'other))"
                  "(setf *published* (slot-value root 'inventory)) 17"
                  "(lambda () (slot-value root 'inventory))"
                  "(setf (slot-value root 'other) (slot-value root 'inventory))
                   (fill (slot-value root 'other) nil :start 8) 17"))
    (private-container-control body body :refuse t
                               :extra (when (search "*published*" body) "((defvar *published* nil))")))
  ;; The visible view contains only NIL, but ARRAY-DISPLACEMENT can reveal a
  ;; private record in its backing. Its exceptional/result boundary is private.
  (private-container-control :displaced-result "(slot-value root 'inventory)" :kind :displaced :refuse t)
  (private-container-control :list-bounds "(fill (slot-value root 'inventory) nil :start 8) 17" :kind :list :refuse t)
  (private-container-control :private-native-import "17" :import-inventory t :refuse t))

(defun private-container-fresh-test (unit)
  (let ((root (asdf:system-source-directory "snowgrave"))
        (cache (merge-pathnames "snowgrave-private-container-fresh/" (uiop:temporary-directory))))
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
                                       (identity (getf data :identity))
                                       (entry (find "ENTRY" (getf data :entries) :test #'string=
                                                    :key (lambda (row) (symbol-name (getf row :name)))))
                                       (key (getf entry :bound-code-key))
                                       (backing (vector 91 92)))
                                  (assert (not (find-class (find-symbol "ANCHOR" (symbol-package (getf entry :name))) nil)))
                                  (snowgrave:with-native-bindings (identity (list (list :backing backing)))
                                    (load (if (uiop:command-line-arguments) artifact ,source)))
                                  (assert (equal '(t t t 17)
                                                 (multiple-value-list
                                                  (funcall (fdefinition (find-symbol (second key) (first key)))))))
                                  (assert (every #'null backing))
                                  ;; Cold inspection of ordinary installed
                                  ;; data checks the inventory's actual joint
                                  ;; aliases/cycle, including its cons edge.
                                  (let ((seen (make-hash-table :test #'eq)) (found nil)
                                        (slot (find-symbol "INVENTORY" (symbol-package (getf entry :name)))))
                                    (labels ((visit (object)
                                               (unless (gethash object seen)
                                                 (setf (gethash object seen) t)
                                                 (cond ((snowgrave:sg-record-p object)
                                                        (let ((inventory (ignore-errors (snowgrave:sg-record-read object slot))))
                                                          (when (and (vectorp inventory) (= 3 (length inventory)))
                                                            (assert (eq object (aref inventory 1)))
                                                            (assert (eq (car (aref inventory 0)) (aref inventory 2)))
                                                            (assert (snowgrave:sg-record-p (aref inventory 2)))
                                                            (setf found t))))
                                                       ((consp object) (visit (car object)) (visit (cdr object)))
                                                       ((arrayp object)
                                                        (dotimes (i (array-total-size object))
                                                          (visit (row-major-aref object i))))))))
                                      (do-symbols (symbol (find-package (first key)))
                                        (when (and (eq (symbol-package symbol) (find-package (first key)))
                                                   (boundp symbol)) (visit (symbol-value symbol))))
                                    (assert found)))
                                (assert (not (let ((package (find-package "SNOWGRAVE.SBCL")))
                                               (and package
                                                    (let ((name (find-symbol "CLOSE-SOURCE" package)))
                                                      (and name (fboundp name)))))))))
                              (format t "Fresh private inventory checked.~%")))
                     (write form :stream driver-stream :readably t) (terpri driver-stream))
                   (finish-output driver-stream)
                   (dolist (mode '(nil "fasl"))
                     (check (search "Fresh private inventory checked."
                                    (uiop:run-program
                                     (append (list "sbcl" "--no-sysinit" "--no-userinit" "--script" (namestring driver))
                                             (when mode (list mode)))
                                     :output :string :error-output *error-output*)))))
              (when (probe-file fasl) (delete-file fasl)))))))))
