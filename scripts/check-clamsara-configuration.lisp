;;; Bind each collector once, audit direct calls, poison the base selectors,
;;; then collect a populated chain repeatedly. Run with a 1024 MiB host heap.
(require :asdf)
(let ((root (uiop:pathname-parent-directory-pathname
             (uiop:pathname-directory-pathname *load-truename*))))
  (asdf:load-asd (merge-pathnames "snowgrave.asd" root))
  (asdf:load-system "snowgrave")
  (asdf:load-system "snowgrave/host-tools")
  (load (merge-pathnames "scripts/clamsara-source.lisp" root))
  (uiop:symbol-call :snowgrave.clamsara-source :register-clamsara-checkout
                    (uiop:symbol-call :snowgrave.clamsara-source :clamsara-checkout)))
(asdf:load-system "clamsara/word-memory")

(defpackage #:snowgrave.clamsara-configuration
  (:use #:cl #:snowgrave.clamsara-source #:snowgrave.host-tools #:clamsara #:clamsara.word-memory))
(in-package #:snowgrave.clamsara-configuration)

(defparameter *workload*
  '((defun fixture (family format n)
      (let* ((domain (make-local-domain))
             (bytes (* n 64))
             (model (if (eq format :pair)
                        (make-pair-memory domain (* (if (eq family :cheney) 2 1) bytes))
                        (make-headered-memory domain (* (if (eq family :cheney) 2 1) bytes))))
             (allocator (if (eq family :cheney) (make-bump-allocator model 0 bytes)
                            (make-pool-allocator model 0 bytes 64)))
             (collector (if (eq family :cheney)
                            (make-cheney allocator (make-bump-allocator model bytes (* 2 bytes)))
                            (make-mark-sweep allocator)))
             (roots (make-vector-roots domain (vector nil))))
        (values model allocator collector roots)))
    (defun populate (model allocator roots n)
      (let ((head nil))
        (dotimes (i n)
          (setf head (if (typep model 'pair-memory)
                         (allocate-pair allocator head (- -1 i))
                         (allocate-node allocator (vector head) (vector (- -1 i))))))
        (setf (aref (root-values roots) 0) head)))
    (defun verify-chain (model roots n)
      (let ((reference (aref (root-values roots) 0)))
        (dotimes (i n)
          (assert (= (if (typep model 'pair-memory) (reference-field model reference 1)
                         (payload-word model reference 0)) (- (- n i))))
          (setf reference (reference-field model reference 0)))
        (assert (null reference))
        (1+ n)))
    (defun cycle (collector roots)
      (acquire-protection (collector-domain collector) collector)
      (unwind-protect (collect collector roots)
        (release-protection (collector-domain collector) collector)))))

(defparameter *roles*
  '((clamsara:collector clamsara::domain)
    (clamsara:precise-collector clamsara::model)
    (clamsara:object-model clamsara::domain)
    (clamsara:allocator clamsara::model clamsara::requests)
    (clamsara:cheney (clamsara::source clamsara::destination))
    (clamsara:mark-sweep clamsara::allocator clamsara::marks clamsara::pending)
    (clamsara:mark-storage clamsara::domain)
    (clamsara:pending-storage clamsara::domain)
    (clamsara:vector-roots clamsara::domain)))

(defun measure (label family format function)
  (dotimes (i 30) (funcall function))
  (host-gc)
  (dotimes (i 30) (funcall function))
  (let ((before (host-bytes-consed)) (start (get-internal-real-time)))
    (dotimes (i 100) (funcall function))
    (let ((bytes (and before (- (host-bytes-consed) before)))
          (ms (* 10d0 (/ (- (get-internal-real-time) start) internal-time-units-per-second))))
      (format t "~&~A ~S ~S n=8192 bytes=~A ms/collection=~,3F~%" label family format bytes ms)
      (when bytes (assert (zerop bytes))))))

(mapc #'eval *workload*)
(defparameter *unit*
  (let* ((forms (append (mapcan #'read-definitions
                                (append (source-files (asdf:find-system "clamsara"))
                                        (source-files (asdf:find-system "clamsara/word-memory"))))
                        *workload*)))
    (snowgrave:close-source-unit
     (list :forms forms) :unit-name :clamsara-configurations
     :universe (loop for form in forms when (eq (first form) 'defclass) collect (second form))
     :entries '(fixture populate verify-chain cycle)
     :external-domains '((fixture (symbol symbol integer)) (populate (t t t integer))
                         (verify-chain (t t integer)) (cycle (t t))))))

(defparameter *cases* nil)
(dolist (family '(:cheney :sweep))
  (dolist (format '(:pair :headered))
    (multiple-value-bind (model allocator collector roots) (fixture family format 8192)
      (populate model allocator roots 8192)
      (measure :native family format (lambda () (cycle collector roots)))
      (assert (= 8193 (verify-chain model roots 8192))))
    (multiple-value-bind (model allocator collector roots)
        (funcall (snowgrave:unit-function *unit* 'fixture) family format 8192)
      (funcall (snowgrave:unit-function *unit* 'populate) model allocator roots 8192)
      (let* ((start (get-internal-real-time))
             (cycle (snowgrave:bind-entry *unit* 'cycle (list collector roots) :roles *roles*))
             (verify (snowgrave:bind-entry *unit* 'verify-chain (list model roots 8192) :roles *roles*)))
        (format t "~&BOUND ~S ~S ms=~,3F~%" family format
                (* 1000d0 (/ (- (get-internal-real-time) start) internal-time-units-per-second)))
        (finish-output)
        (push (list family format cycle verify) *cases*)))))

;; A direct entry must not call either the original CLOS generic or its
;; general closed selector. Keep both poisoned while all bindings coexist.
(dolist (plan (snowgrave::unit-plan-generics (snowgrave::closed-unit-plan *unit*)))
  (let ((poison (lambda (&rest args) (declare (ignore args)) (error "Base selector reached.")))
        (original (fdefinition (snowgrave::generic-plan-source plan))))
    (when (typep original 'generic-function)
      (closer-mop:set-funcallable-instance-function original poison))
    (setf (fdefinition (snowgrave::generic-plan-source plan)) poison
          (fdefinition (snowgrave::generic-plan-name plan)) poison)))
(let ((checks 0))
  (dolist (case (nreverse *cases*))
    (destructuring-bind (family format cycle verify) case
      (measure :configured family format cycle)
      (incf checks (funcall verify))))
  (format t "~&Configured Clamsara: ~D chain checks; four simultaneous bindings passed.~%" checks))
