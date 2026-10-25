(in-package #:snowgrave)

;;; Resolve owned calls, method cells, and physical slots before compilation.

(defun specialize-owned-call (configuration name arguments facts)
  (when (some (lambda (fact) (let ((callable (fact-callable fact)))
                               (and callable (not (function-name-p callable))))) facts)
    (unsupported :configuration-indirect-call "A lexical closure needs explicit capture conversion before crossing an owned helper."))
  (let* ((key (list name (mapcar #'fact-key facts)))
         (table (configuration-specializations configuration))
         (existing (gethash key table)))
    (when existing
      (return-from specialize-owned-call
        (values (cons (specialization-name existing) arguments)
                (or (specialization-fact existing) (make-fact)))))
    (let* ((definition (gethash name (configuration-functions configuration)))
           (target (intern (format nil "~A.~D" (if (consp name) (symbol-name (second name)) (symbol-name name))
                                   (hash-table-count table))
                           (symbol-package (configuration-entry configuration))))
           (parameters (loop repeat (length arguments) collect (gensym "INPUT")))
           (item (make-specialization :name target)))
      (unless definition (unsupported :configuration-source "Missing owned source for ~S." name))
      ;; Generated component/role captures are introduced later. Authored
      ;; load-time code must not bypass configured call and escape auditing.
      (when (authored-load-time-value-p (cddr definition))
        (unsupported :configuration-form "Authored LOAD-TIME-VALUE needs explicit cold realization."))
      ;; Publish the recursive name before walking its body. Recursion uses a
      ;; conservative result fact; it does not run a field/state fixed point.
      (setf (gethash key table) item)
      (multiple-value-bind (body fact)
          (specialize-lambda-call configuration (cddr definition) parameters facts nil
                                  (if (consp name) (second name) name))
        (when (and (fact-callable fact) (not (function-name-p (fact-callable fact))))
          (unsupported :configuration-indirect-call "An escaping lexical closure needs explicit capture conversion."))
        (setf (specialization-fact item) fact
              (specialization-source item)
              `(defun ,target ,parameters
                 ,@(let ((types (loop for parameter in parameters for value in facts
                                      unless (eq (fact-type value) t) collect `(type ,(fact-type value) ,parameter))))
                     (when types (list (cons 'declare types))))
                 ,body))
        (push item (configuration-emitted configuration))
        (values (cons target arguments) fact)))))

(defun configured-axis-indices (axis type)
  (let ((excluded nil) (result nil))
    (loop for (kind expected) in axis for index from 0
          for domain = (if (member kind '(:any :other)) `(not (or ,@excluded))
                           `(and ,expected (not (or ,@excluded))))
          do (unless (subtypep `(and ,type ,domain) nil) (push index result))
             (unless (member kind '(:any :other)) (push expected excluded)))
    (nreverse result)))

(defun specialize-generic-call (configuration plan arguments facts environment)
  (let* ((required (getf plan :required)) (supplied (- (length arguments) required))
         (indices '(0)))
    (unless (and (not (getf plan :variable-tail)) (<= 0 supplied (getf plan :optional)))
      (unsupported :configuration-variable-tail "Configured generic ~S needs a bounded argument prefix." (getf plan :source)))
    (loop for axis in (getf plan :axes) for fact in facts
          do (setf indices (loop for prefix in indices append
                            (loop for coordinate in (configured-axis-indices axis (fact-type fact))
                                  collect (+ (* prefix (length axis)) coordinate)))))
    (let* ((clauses (remove-duplicates
                     (mapcar (lambda (index)
                               (find-if (lambda (clause) (member index (first clause))) (getf plan :clauses))) indices)))
           (clause (first clauses)))
      (unless (and clause (= (length clauses) 1))
        (unsupported :configuration-dispatch "Unresolved method selection for ~S with ~S."
                     (getf plan :source) (mapcar #'fact-type facts)))
      (specialize-lambda-call
       configuration
       (list (append (getf plan :arguments)
                     (when (getf plan :optional-count) (list (getf plan :optional-count)))
                     (list (getf plan :overflow)))
             (canonical-source (cons 'progn (rest clause))))
       (append arguments (make-list (- (+ required (getf plan :optional)) (length arguments)))
               (when (getf plan :optional-count) (list supplied)) (list nil))
       (append facts (loop repeat (- (+ required (getf plan :optional)) (length facts)) collect (literal-fact nil))
               (when (getf plan :optional-count) (list (literal-fact supplied))) (list (literal-fact nil)))
       environment))))

(defun specialize-slot-call (configuration plan arguments facts environment)
  (let* ((object-index (if (eq (getf plan :operation) :write) 1 0))
         (type (fact-type (nth object-index facts)))
         (cases (getf plan :cases))
         (row (find-if (lambda (row) (subtypep type (first row))) cases))
         (unique (and (null row) (= (length cases) 1))))
    (unless (or row unique)
      (unsupported :configuration-dispatch "Unresolved physical slot ~S on ~S." (getf plan :slot) type))
    (setf row (or row (first cases)))
    (let* ((body (configured-slot-body configuration plan row))
           (roles (gethash (third row) (configuration-fields configuration)))
           (values (remove-duplicates (loop for row in roles append (copy-list (cdr row)))))
           (result (case (getf plan :operation)
                     (:read (if roles (make-fact :type `(or ,@(mapcar (lambda (value) (class-name (class-of value))) values)))
                                (make-fact)))
                     (:write (first facts))
                     (:unbind (nth object-index facts))
                     (otherwise (make-fact :type 'boolean)))))
      (when unique
        (setf body `(if (,(second row) ,(getf plan :object)) ,body
                       (,(getf plan :invalid) ,(getf plan :object) ',(getf plan :slot)))))
      (values (specialize-lambda-call configuration (list (getf plan :arguments) (canonical-source body)) arguments facts environment)
              result))))

(defun specialize-known-call (configuration name arguments facts environment)
  (let ((local (cdr (assoc name (getf environment :functions) :test #'equal)))
        (generic (configuration-plan configuration :generics name))
        (slot (configuration-plan configuration :slots name)))
    (cond (local (specialize-local-call configuration local arguments facts))
          (generic (specialize-generic-call configuration generic arguments facts environment))
          (slot (specialize-slot-call configuration slot arguments facts environment))
          ((or (member name (configuration-data configuration :construction-functions) :test #'equal)
               (find name (configuration-data configuration :layouts) :key (lambda (layout) (getf layout :allocator))))
           (unsupported :configuration-allocation "Configured entry reaches component construction ~S." name))
          ((and (gethash name (configuration-functions configuration))
                (not (member name (configuration-data configuration :slow-paths) :test #'equal)))
           (specialize-owned-call configuration name arguments facts))
          (t (audit-native-callbacks configuration name arguments facts)
             (values (if (consp name) `(funcall #',name ,@arguments) (cons name arguments))
                     (cond ((eq name 'identity) (or (first facts) (make-fact)))
                           ((and (member name '(eq eql not null)) (every #'fact-known facts))
                            (literal-fact (apply (fdefinition name) (mapcar #'fact-value facts))))
                           ((member name '(eq eql not null typep)) (make-fact :type 'boolean))
                           (t (make-fact))))))))

(defun audit-native-callbacks (configuration name arguments facts)
  (dolist (fact facts)
    (audit-callable-transfer configuration fact name))
  (labels ((check (position)
             (let ((callee (fact-callable (nth position facts))))
               (unless (and callee (function-name-p callee)
                            (not (gethash callee (configuration-functions configuration))))
                 (unsupported :configuration-indirect-call "Unresolved callback to ~S." name)))))
    (dolist (position (rest (assoc name *callback-arguments*))) (check position))
    (let ((start (cdr (assoc name *callback-keywords*))))
      (when start
        (loop for position from start below (length arguments) by 2
              for key = (nth position facts)
              do (unless (fact-known key)
                   (unsupported :configuration-indirect-call "Computed callback keyword for ~S." name))
                 (when (member (fact-value key) '(:key :test :test-not))
                   (unless (and (eq (fact-value (nth (1+ position) facts)) nil)
                                (fact-known (nth (1+ position) facts)))
                     (check (1+ position)))))))))
