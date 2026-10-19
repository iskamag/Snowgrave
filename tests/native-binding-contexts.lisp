(in-package #:snowgrave.tests)

(defun native-context-manifest (keys)
  (list :resources (loop for key in keys for id from 0 collect (list :key key :node id))
        :nodes (loop for key in keys for id from 0 collect
                 (list :id id :path (list :resource key) :kind :array :dimensions '(1)
                       :element-type t :adjustable nil :has-fill-pointer nil :backing nil :offset 0))))

(defun native-context-resolve (identity manifest)
  (snowgrave::%resolve-native-bindings identity manifest))

(defun native-binding-context-tests ()
  ;; Keys and unit identities are owned structural data; resource values keep
  ;; their actual identities. Mutating the caller's key cannot rename a scope.
  (let* ((name (copy-seq "native-unit")) (key-name (copy-seq "region"))
         (identity (list :context name)) (key (list :arena key-name))
         (manifest (native-context-manifest '((:arena "region"))))
         (resource (vector 17)))
    (snowgrave:with-native-bindings (identity (list (list key resource)))
      (setf (char name 0) #\X (char key-name 0) #\X (aref resource 0) 23)
      (let ((roots (native-context-resolve '(:context "native-unit") manifest)))
        (check (eq resource (aref roots 0)))
        (check (= 23 (aref (aref roots 0) 0))))))
  ;; Equal composite keys collide even if their conses/strings are distinct.
  (entry-graph-refusal
   (lambda ()
     (snowgrave:with-native-bindings
         ('(:duplicate-context)
          (list (list (list :arena (copy-seq "same")) (vector 1))
                (list (list :arena (copy-seq "same")) (vector 2))))
       (error "Duplicate native key was admitted.")))
   :native-binding-context)
  ;; Dynamic scopes restore their predecessor on abrupt exit. A resolver does
  ;; not retain that scope after it ends; installed artifact roots do so instead.
  (let* ((identity '(:nested-context)) (manifest (native-context-manifest '(:data)))
         (outer (vector 1)) (inner (vector 2)))
    (snowgrave:with-native-bindings (identity (list (list :data outer)))
      (check (eq outer (aref (native-context-resolve identity manifest) 0)))
      (check (eq :unwound
                 (catch 'native-context-exit
                   (snowgrave:with-native-bindings (identity (list (list :data inner)))
                     (check (eq inner (aref (native-context-resolve identity manifest) 0)))
                     (throw 'native-context-exit :unwound)))))
      (check (eq outer (aref (native-context-resolve identity manifest) 0))))
    (entry-graph-refusal (lambda () (native-context-resolve identity manifest)) :native-binding-missing))
  ;; Manifest order owns the returned vector, independently of the caller's
  ;; binding order or the implementation's key index iteration order.
  (let* ((keys (loop for index below 256 collect (list :arena index)))
         (bindings (loop for key in keys for index from 0 collect (list key (vector index))))
         (manifest (native-context-manifest keys)) (identity '(:ordered-context)))
    (snowgrave:with-native-bindings (identity (reverse bindings))
      (let ((roots (native-context-resolve identity manifest)))
        (check (= 256 (length roots)))
        (check (loop for binding in bindings for root across roots always (eq (second binding) root)))
        (check (loop for root across roots for index from 0 always (= index (aref root 0))))))
    (entry-graph-refusal
     (lambda ()
       (snowgrave:with-native-bindings (identity (rest bindings))
         (native-context-resolve identity manifest))) :native-binding-missing)
    (entry-graph-refusal
     (lambda ()
       (snowgrave:with-native-bindings (identity (cons (list :unexpected (vector 9)) (rest bindings)))
         (native-context-resolve identity manifest))) :native-binding-missing)))
