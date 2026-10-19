;;;; Synthetic cold-mapper fixture, not an authored-unit/supervisor proof.
(defpackage #:snowgrave.native-layout-proof (:use #:cl))
(in-package #:snowgrave.native-layout-proof)

(snowgrave.mezzano-materializer:define-materialized-unit
 (:identity (:native-layout-proof)
  :record-layouts
  ((:identity ((:native-layout-proof) cell :version 1)
    :class cell :class-token :native-layout-cell :ancestors (cell)
    :slots (payload) :slot-types ((unsigned-byte 8)) :error-mapping nil)))
 ((defparameter *expected-layout*
    (snowgrave:make-layout '((:native-layout-proof) cell :version 1) 'cell '(cell) '(payload)
                          :slot-types '((unsigned-byte 8)) :error-mapping 'nil))
  (defun matches-admitted-layout (record)
    (snowgrave:sg-record-matches-layout-p record *expected-layout*)))
 :wired)
