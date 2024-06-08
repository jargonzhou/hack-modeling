;;;; 队列
;;;; 一个cons的car和cdr分别指向列表头部和尾部.


(in-package :common-lisp-user)


(defun make-queue () (cons nil nil))

(defun enqueue (obj q)
  (if (null (car q))
      (setf (cdr q) (setf (car q) (list obj)))
      (setf (cdr (cdr q)) (list obj)
	    (cdr q) (cdr (cdr q))))
  (car q))


(defun dequeue (q)
  (pop (car q)))


(let ((q (make-queue)))
  (enqueue 'a q)
  (print q)
  (enqueue 'b q)
  (print q)
  (enqueue 'c q)
  (print q)
  (dequeue q)
  (print q)
  (dequeue q)
  (print q)
  (dequeue q)
  (print q)
  (dequeue q)
  (print q))
