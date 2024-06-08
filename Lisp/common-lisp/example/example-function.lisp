; ---------------------------------------------------------------------------
; 函数
; ---------------------------------------------------------------------------

(defun hello-world () (format t "hello, world~%"))
(hello-world)

(defun verbose-sum (x y)
  "sum any two numbers"
  (format t "Summing ~d and ~d.~%" x y)
  (+ x y))
(verbose-sum 1 2)

					; 可选形参
(defun foo (a b &optional c d) (list a b c d))
(foo 1 2) ; (1 2 NIL NIL)
(foo 1 2 3) ; (1 2 3 NIL)
(foo 1 2 3 4) ; (1 2 3 4)

(defun foo2 (a &optional (b 10)) (list a b)) ; 带默认值
(foo2 1) ; (1 10) 
(foo2 1 20) ; (1 20)

(defun foo3 (a b &optional (c 3 c-supplied-p))
  (list a b c c-supplied-p))
(foo3 1 2) ; (1 2 3 NIL)
(foo3 1 2 3) ; (1 2 3 T)
(foo3 1 2 4) ; (1 2 4 T)

					; 剩余形参
(defun foo4 (a &rest values) (list a values))
(foo4 1) ; (1 NIL)
(foo4 1 2) ; (1 (2))
(foo4 1 2 3) ; (1 (2 3))

					; 关键字形参
(defun foo5 (&key a b c) (list a b c))
(foo5) ; (NIL NIL NIL)
(foo5 :a 1) ; (1 NIL NIL)
(foo5 :b 1) ; (NIL 1 NIL)
(foo5 :c 1) ; (NIL NIL 1)
(foo5 :a 1 :c 3) ; (1 NIL 3)
(foo5 :a 1 :b 2 :c 3) ; (1 2 3)
(foo5 :a 1 :c 3 :b 2) ; (1 2 3)

(defun foo6 (&key (a 0) (b 0 b-supplied-p) (c (+ a b)))
  (list a b c b-supplied-p))
(foo6 :a 1) ; (1 0 1 NIL)
(foo6 :b 1) ; (0 1 1 T)
(foo6 :b 1 :c 4) ; (0 1 4 T)
(foo6 :a 2 :b 1 :c 3) ; (0 1 4 T)

					; 函数返回值

(defun foo7 (n)
  (dotimes (i 10)
    (dotimes (j 10)
      (when (> (* i j) n)
	(return-from foo7 (list i j))))))
(foo7 10) ; (2 6)

					; 高阶函数

(defun foo8 (x) (* 2 x))
(function foo8) ; #<FUNCTION FOO8>
#'foo8 ; #<FUNCTION FOO8>
(funcall #'foo8 2) ; 4

(defun plot (fn min max step)
  (loop for i from min to max by step do
       (loop repeat (funcall fn i) do (format t "*"))
       (format t "~%")))
(plot #'exp 0 4 1/2)
(apply #'plot #'exp '(0 4 1/2))
(apply #'plot '(exp 0 4 1/2))


					; 匿名函数
((lambda (x y) (+ x y)) 2 3) ; 5
(funcall #'(lambda (x y) (+ x y)) 2 3) ; 5
(defun doubles (x) (* 2 x))
(plot #'doubles 0 10 1)









