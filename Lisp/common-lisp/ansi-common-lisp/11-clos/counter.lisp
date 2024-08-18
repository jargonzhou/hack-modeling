;;;; 演示CLOS的封装

(in-package :common-lisp-user)

(defpackage :com.spike.cl.ansi-cl.ctr
  (:use :common-lisp)
  (:export :counter :increment :clear))

(in-package :com.spike.cl.ansi-cl.ctr)

(defclass counter () ((state :initform 0)))

(defmethod increment ((c counter))
  (incf (slot-value c 'state)))

(defmethod clear ((c counter))
  (setf (slot-value c 'state) 0))
