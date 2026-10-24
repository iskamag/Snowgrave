(in-package #:snowgrave)

;;; Keep the binding transformation independent of the host's compiler and
;;; walker representation. CL-FORM-TYPES supplies lexical traversal through
;;; the portable CL-ENVIRONMENTS interface; no inferred compiler IR is used.
(defvar *source-local-functions* nil)

(defparameter *standard-native-places* '(aref svref sbit bit gethash))

(defun restore-native-place (form)
  ;; SETF expansions may use setter functions that other hosts do not define.
  ;; Preserve the expansion's value-first operand order with fresh temporaries.
  (if (and (consp form) (eq (first form) 'funcall)
           (consp (second form)) (eq (caadr form) 'function)
           (consp (cadadr form)) (eq (first (cadadr form)) 'setf)
           (member (second (cadadr form)) *standard-native-places*))
      (let ((arguments (loop repeat (length (cddr form)) collect (gensym "STORE"))))
        `(let ,(mapcar #'list arguments (cddr form))
           (setf (,(second (cadadr form)) ,@(rest arguments)) ,(first arguments))))
      form))

(defun source-local-function-p (name environment)
  (or (and environment (member name *source-local-functions* :test #'equal))
      ;; The CLTL2 compatibility API on some hosts only accepts symbol names.
      ;; SETF lexical names are tracked by the standard FLET/LABELS contours.
      (and (symbolp name) (nth-value 1 (cl-environments:function-information name environment)))))

(defun source-lexical-variable-p (name environment)
  (eq (cl-environments:variable-information name environment) :lexical))

(defun protect-record-places (form)
  ;; Let the host implement modifying macros, but present SLOT-VALUE as an
  ;; ordinary functional place. Their expansions then retain a portable SETF
  ;; function call instead of embedding the host's private CLOS writer.
  (labels ((place (node)
             (cond ((atom node) node)
                   ((eq (first node) 'quote) node)
                   (t (cons (if (eq (first node) 'slot-value) '%source-slot-value (first node))
                            (mapcar #'place (rest node)))))))
    (when (consp form)
      (case (first form)
        ((incf decf pop) (list* (first form) (place (second form)) (cddr form)))
        ((push pushnew) (list* (first form) (second form) (place (third form)) (cdddr form)))
        ((rotatef) (cons (first form) (mapcar #'place (rest form))))
        ((shiftf) (append (list (first form)) (mapcar #'place (butlast (rest form))) (last form)))
        ((psetf) (cons (first form) (loop for (target value) on (rest form) by #'cddr
                                        append (list (place target) value))))))))

(defun restore-record-place (form)
  (cond ((and (consp form) (eq (first form) '%source-slot-value))
         (cons 'slot-value (rest form)))
        ((and (consp form) (eq (first form) 'funcall)
              (equal (second form) '(function (setf %source-slot-value))))
         (let ((value (gensym "NEW")) (object (gensym "OBJECT")) (slot (gensym "SLOT")))
           `(let* ((,value ,(third form)) (,object ,(fourth form)) (,slot ,(fifth form)))
              (setf (slot-value ,object ,(if (and (consp (fifth form)) (eq (car (fifth form)) 'quote))
                                            (fifth form) slot)) ,value))))
        (t form)))

(defun walk-standard-control (form environment function)
  ;; These standard forms carry condition/restart bindings. Preserve their
  ;; portable syntax instead of expanding the host's condition machinery.
  (labels ((walk (node) (walk-source-form node environment function))
           (body (forms) (rest (walk (cons 'locally forms))))
           (binding-body (lambda-list forms)
             (rest (walk (list* 'lambda lambda-list forms)))))
    (case (first form)
      (multiple-value-bind
       ;; Keep the standard binding form visible to the target compiler.
       ;; Some hosts expand it into a heap-allocated closure under MVCALL.
       (let ((bound (binding-body (second form) (cdddr form))))
         (values `(multiple-value-bind ,(first bound) ,(walk (third form)) ,@(rest bound)) t)))
      ((handler-bind restart-bind)
       (values `(,(first form)
                 ,(loop for (name value . options) in (second form)
                        collect `(,name ,(walk value)
                                       ,@(loop for (key value) on options by #'cddr append (list key (walk value)))))
                 ,@(body (cddr form))) t))
      (handler-case
       (values `(handler-case ,(walk (second form))
                  ,@(loop for (type lambda-list . forms) in (cddr form)
                          collect (cons type (binding-body lambda-list forms)))) t))
      (restart-case
       (values `(restart-case ,(walk (second form))
                  ,@(loop for (name lambda-list . forms) in (cddr form)
                          collect (let ((options nil))
                                    (loop while (keywordp (first forms))
                                          do (push (pop forms) options) (push (walk (pop forms)) options))
                                    (let ((body (binding-body lambda-list forms)))
                                      `(,name ,(first body) ,@(nreverse options) ,@(rest body)))))) t))
      (assert
       (values `(assert ,(walk (second form))
                  ,(mapcar #'walk (third form)) ,@(mapcar #'walk (cdddr form))) t))
      (check-type
       (values `(check-type ,(walk (second form)) ,(third form) ,@(cdddr form)) t)))))

(defun walk-source-form (form environment function)
  (labels ((visit (node env)
             (setf node (restore-native-place (restore-record-place (normalize-host-expression node))))
             (let ((protected (protect-record-places node)))
               (when (and protected (not (equal protected node)))
                 (return-from visit (values (walk-source-form protected env function) t))))
             (multiple-value-bind (replacement stop) (funcall function node :eval env)
               (when stop (return-from visit (values replacement t)))
               (when (consp replacement)
                 (multiple-value-bind (control handled) (walk-standard-control replacement env function)
                   (when handled (return-from visit (values control t)))))
               (cond
                 ((and (consp replacement) (member (first replacement) '(flet labels)))
                  (let* ((names (mapcar #'first (second replacement)))
                         (inner (cl-environments:augment-environment env :function names))
                         (definitions
                           (loop for definition in (second replacement)
                                 collect
                                 (let ((*source-local-functions*
                                         (if (eq (first replacement) 'labels)
                                             (append names *source-local-functions*) *source-local-functions*)))
                                   (cons (first definition)
                                         (rest (walk-source-form (cons 'lambda (rest definition))
                                                                 (if (eq (first replacement) 'labels) inner env)
                                                                 function)))))))
                    (let ((*source-local-functions* (append names *source-local-functions*)))
                      (values `(,(first replacement) ,definitions
                                 ,@(rest (walk-source-form (cons 'locally (cddr replacement)) inner function))) t))))
                 ((and (consp replacement) (eq (first replacement) 'setq))
                  (values `(progn
                             ,@(loop for (name value) on (rest replacement) by #'cddr
                                     collect
                                     (multiple-value-bind (expanded changed)
                                         (cl-environments:macroexpand-1 name env)
                                       (if changed
                                           (walk-source-form `(setf ,expanded ,value) env function)
                                           `(setq ,(funcall function name :set env)
                                                  ,(walk-source-form value env function)))))) t))
                 ((and (consp replacement) (eq (first replacement) 'setf)
                       (loop for (place value) on (rest replacement) by #'cddr
                             thereis (and (consp place) (member (first place) '(slot-value aref svref sbit bit gethash)))))
                  ;; Keep this standard place visible to the closing pass.
                  ;; Native SETF expansions often hide it in a CLOS primitive.
                  (values `(progn
                             ,@(loop for (place value) on (rest replacement) by #'cddr
                                     collect
                                     (if (and (consp place) (member (first place) '(slot-value aref svref sbit bit gethash)))
                                         `(setf (,(first place)
                                                 ,@(mapcar (lambda (part) (walk-source-form part env function))
                                                           (rest place)))
                                                ,(walk-source-form value env function))
                                         (walk-source-form `(setf ,place ,value) env function)))) t))
                 ((and (consp replacement) (eq (first replacement) 'function)
                       (consp (second replacement)) (eq (caadr replacement) 'lambda))
                  (multiple-value-bind (lambda-form done)
                      (funcall function (second replacement) :eval env)
                    (values (list 'function lambda-form) done)))
                 (t replacement)))))
    (if (and (consp form) (eq (first form) 'lambda))
        (second (cl-form-types.walker:walk-form #'visit (list 'function form) environment))
        (cl-form-types.walker:walk-form #'visit form environment))))
