;;;; 控制结构

(in-package :com.spike.language.cl.snippets)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 块: progn, block, tagbody
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(progn
  (format t "a")
  (format t "b")
  (+ 11 12))

(block head
  (format t "Here we go.")
  (return-from head 'idea)
  (format t "We'll never see this."))

(block nil
  (return 27))

;; 有些操作符有隐式的nil block体
(dolist (x '(a b c d e))
  (format t "~A " x)
  (if (eql x 'c)
      (return 'done)))

(defun foo ()
  (return-from foo 27))
(foo)


;; tagbody, go
(let ((x))
  (tagbody
     (setf x 0)
   top ; label
     (setf x (+ x 1))
     (format t "~A " x)
     (if (< x 10) (go top))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 上下文: let, let*, destructuring-bind
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(let ((x 7)
      (y 2))
  (format t "Number")
  (+ x y))
;; 像一个函数调用
((lambda (x y)
   (format t "Number")
   (+ x y))
   7
   2)


(let* ((x 1)
       (y (+ x 1)))
  (+ x y))

(let ((x 0))
  (let* ((y (+ x 1)) ; not (x 1)!!!
	 (x 1))
    (+ x y)))
;; 嵌套的let
(let ((x 1))
  (let ((y (+ x 1)))
    (+ x y)))


;; 解构绑定
(destructuring-bind (w (x y) . z) '(a (b c) d e)
  (list w x y z))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 条件化: if, when, cond, case
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(let ((that 1))
  (when (oddp that)
    (format t "Hmm, that's odd.")
    (+ that 1)))

(let ((that 1))
  (if (oddp that)
      (progn
	(format t "Hmm, that's odd.")
	(+ that 1))))


(defun our-member2 (obj lst)
  (cond ((atom lst) nil)
	((eql (car lst) obj) lst)
	(t (our-member2 obj (cdr lst)))))
(our-member2 1 '(1 2 3))

(cond (99))




(defun leap-year (year)
  "https://en.wikipedia.org/wiki/Leap_year

     if (year is not divisible by 4) then (it is a common year)
     else if (year is not divisible by 100) then (it is a leap year)
     else if (year is not divisible by 400) then (it is a common year)
     else (it is a leap year)"
  (if (not (eql 0 (rem year 4)))
      nil
      (if (not (eql 0 (rem year 100)))
	  t
	  (if (not (eql 0 (rem year 400)))
	      nil
	      t))))

(list (leap-year 2000)
      (leap-year 2001)
      (leap-year 2002)
      (leap-year 2003)
      (leap-year 2004))

;; 键被视为常量, 默认的分支为t或otherwise
(defun month-length (mon)
  (case mon
    ((jan mar may jul aug oct dec) 31)
    ((apr jun sept nov) 30)
    (feb (if (current-leap-year) 29 28))
    (otherwise "unknown month")))

(defun current-leap-year ()
  (multiple-value-bind (s min h d mon y dow dstf tz) (get-decoded-time)
    (leap-year y)))

(get-decoded-time)
(current-leap-year)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 迭代: do, do*, dolist, dotimes, mapc
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun show-squares (start end)
  (do ((i start (+ i 1)))
      ((> i end) 'done)
    (format t "~A ~A~%" i (* i i))))

(show-squares 1 10)


;; (1 A) (2 1) (3 2) (4 3) (5 4)
;; y的值引用do引入的x的前一个迭代的值
(let ((x 'a))
  (do ((x 1 (+ x 1))
       (y x x))
      ((> x 5))
    (format t "(~A ~A) " x y)))

;; (1 1) (2 2) (3 3) (4 4) (5 5) 
;; y的值为当前迭代中x的值
(do* ((x 1 (+ x 1))
      (y x x))
     ((> x 5))
  (format t "(~A ~A) " x y))

(dolist (x '(a b c d) 'done)
  (format t "~A " x))

(dotimes (x 5 x)
  (format t "~A " x))


;; 总是返回第二个参数
(mapc #'(lambda (x y)
	  (format t "~A ~A " x y))
      '(hip flip slip)
      '(hop flop slop))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 多值: values, multiple-value-bind, multiple-value-call, multiple-value-list
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(values 'a nil (+ 2 4))

(let ((x (values 1 2)))
  x)

(values)
(let ((x (values)))
  x)


(multiple-value-bind (x y z) (values 1 2 3)
  (list x y z))
(multiple-value-bind (x y z) (values 1 2)
  (list x y z))
(multiple-value-bind (x y) (values 1 2 3)
  (list x y))


(multiple-value-call #'+ (values 1 2 3))
;; (1 2 3)
(multiple-value-list (values 1 2 3))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; abort: catch, throw, error, unwind-protect
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun super ()
  (catch 'abort
    (sub)
    (format t "We'll never see this.")))

(defun sub()
  (throw 'abort 99))


(super)


;; (progn
;;   (error "Oops!")
;;   (format t "After the error."))

;; 2
(let ((x 1))
  (catch 'abort
    (unwind-protect
	 (throw 'abort 999)
      (setf x 2)))
  x)
