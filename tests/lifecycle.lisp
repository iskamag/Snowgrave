(in-package #:snowgrave.tests)

(defun lifecycle-tests ()
  ;; Reader errors used to escape before the two temporary namespaces entered
  ;; their UNWIND-PROTECT. Also check failure after indexing has begun.
  (dolist (case '(((:invalid-source) :source-unit)
                  ((:forms ((defmacro invalid-entry () 7))) :definition)))
    (let ((packages (list-all-packages)))
      (check-signals (snowgrave:snowgrave-error (second case))
        (snowgrave:close-source-unit (first case) :unit-name :failed-lifecycle
                                    :entries '(invalid-entry) :external-domains '((invalid-entry ())))
        "Failed close reported the wrong feature for ~S" (first case))
      (check (null (set-difference (list-all-packages) packages))
             "Failed close leaked a compilation namespace"))))
