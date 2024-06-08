;;;; 结构

(in-package :com.spike.language.cl.snippets)

;;; 类型层次: point -> structure -> atom -> t
;;; 生成函数: make-point, point-p, copy-point, point-x, point-y
(defstruct point
  x
  y)

(let ((p (make-point :x 0 :y 0)))
  (print (point-p p))       ;T
  (print (point-x p))       ;0
  (print (copy-point p))    ;#S(POINT :X 0 :Y 0) 
  (setf (point-y p) 2)      ;#S(POINT :X 0 :Y 2)
  (print p)                 ;#S(POINT :X 0 :Y 2)
  (print (typep p 'point))) ;T

(defstruct polemic
  (type (progn
	  (format t "What kind of polemic was it? ")
	  (read)))
  (effect nil))

;(make-polemic)


;;; 定制访问函数和输出
;;; point- => p
(defstruct (point-v2 (:conc-name p)
		     (:print-function print-point))
  (x 0)
  (y 0))

(defun print-point (p stream depth)
  (format stream "#<~A, ~A>" (px p) (py p)))

(let ((p (make-point-v2)))
  (print p)) ; #<0, 0>
