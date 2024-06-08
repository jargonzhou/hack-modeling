; ---------------------------------------------------------------------------
; 标准控制构造宏
; ---------------------------------------------------------------------------

					; WHEN, UNLESS

(write-line (if (> 2 3) "Yup" "Nope"))
;(format t (if (> 2 3) "Yup")) ; NIL
(write-line (if (> 3 2) "Yup" "Nope"))

(if (> 3 2)
    (progn
      (write-line "1")
      (write-line "2")))

(when (> 3 2)
  (write-line "1")
  (write-line "2"))

(unless (> 2 3)
  (write-line "1")
  (write-line "2"))



					; COND

(let ((x 3))
  (cond ((> x 4) (write-line ">4"))
	((> x 3) (write-line ">3"))
	((> x 2) (write-line ">2"))))

					; AND, OR, NOT
(not nil)
(and (= 1 2) (= 3 3))
(or (= 1 2) (= 3 3))

					; 循环
(dolist (x '(1 2 3)) (print x))
(dolist (x '(1 2 3)) (print x) (if (evenp x) (return)))

(dotimes (i 4) (print i))
(dotimes (x 20)
  (dotimes (y 20)
    (format t "~3d " (* (1+ x) (1+ y))))
  (format t "~%"))

					; DO
(do ((n 0 (1+ n))
     (cur 0 next)
     (next 1 (+ cur next)))
    ((= 10 n) cur))

					; LOOP
(let ((x 10))
  (loop
     (when (< x 5) (return))
     (print x)
     (decf x)))

(loop for i from 1 to 10 collecting i)
(loop for i below 10
   and a = 0 then b
   and b = 1 then (+ b a)
   finally (return a))

					; custom
(defmacro do-primes ((var start end) &body body)
  `(do ((,var (next-prime ,start) (next-prime (1+ ,var))))
       ((> ,var ,end))
     ,@body))



(defun next-prime (number)
  (loop for n from number when (primep n) return n))
(defun primep (number)
  (when (> number 1)
    (loop for fac from 2 to (isqrt number) never (zerop (mod number fac)))))

(do-primes (p 0 19) (format t "~d " p))
(macroexpand-1 '(do-primes (p 0 19) (format t "~d " p)))



