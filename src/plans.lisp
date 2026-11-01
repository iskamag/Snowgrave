(in-package #:snowgrave)

;;; Internal compiler contracts. Only DISPATCH-CUT contains live MOP objects;
;;; retained unit plans contain source, names, types, and ordinary layout data.
(defstruct unit-plan
  package generics special-variables entries slots accessor-functions slow-paths construction-functions layouts
  function-sources)
(defstruct generic-plan
  name source required optional variable-tail arguments optional-count overflow axes clauses)
(defstruct generic-clause indices body)
(defstruct slot-plan name operation slot arguments invalid object value cases)
(defstruct slot-case type predicate field body)
(defstruct dispatch-cut kind type class excluded)
(defstruct dispatch-domain kind type)
(defstruct lambda-shape required optional rest keyp keys allow)
(defstruct mutation-dependency owners (unknown nil :type boolean))
(defstruct function-source form normalized)
