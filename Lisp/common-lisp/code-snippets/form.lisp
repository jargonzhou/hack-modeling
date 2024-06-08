;;;; 形式

(in-package :com.spike.language.cl.snippets)

;; 1
;; (+ 2 3)
;; (+)
;; (+ 2)
;; (+ 2 3 4)
;; (/ (- 7 1) (- 4 2))

;;;; quote
(quote (+ 3 5))
'(+ 3 5)

;;;; symbol
;; 'Artichoke
;; '(my 3 "Sons")
;; '(the list (a b c) has 3 elements)
;; (list 'my (+ 2 1) "Sons")
;; (list '(+ 2 1) (+ 2 1))
;; ()
;; nil

;;; list operation
;; (cons 'a '(b c d))
;; (cons 'a (cons 'b nil))
;; (list 'a 'b)
;; (car '(a b c))
;; (cdr '(a b c))
;; (car (cdr (cdr '(a b c d))))
;; (third '(a b c d))

;;; truth
;; (listp '(a b c))
;; (listp 27)
;; (null nil)
;; (not nil)

;; (if (listp '(a b c))
;;     (+ 1 2)
;;     (+ 5 6))
;; (if (listp 27)
;;     (+ 1 2)
;;     (+ 5 6))
;; (if (listp 27)
;;     (+ 2 3))
;; (if 27 1 2)

;; ; 7
;; (and t (+ 1 2) (+ 3 4))
;; ; 3
;; (or nil (+ 1 2) (+ 3 4))


;;; function
(defun our-third (x)
  (car (cdr (cdr x))))

(our-third '(a b c d))

(defun sum-greater (x y z)
  (> (+ x y) z))

(sum-greater 1 4 3)

;;; recursion

(defun our-member (obj lst)
  (if (null lst)
      nil
      (if (eql (car lst) obj)
	  lst
	  (our-member obj (cdr lst)))))

(our-member 'b '(a b c))
(our-member 'd '(a b c))

;;; input and output

;; (format t "~A plus ~A equals ~A.~%" 2 3 (+ 2 3))

;; (defun askem (string)
;;   (format t "~A" string)
;;   (read))

;; (askem "How old are you?")


;;; variables

;; (let ((x 1) (y 2))
;;   (+ x y))

;; (defun ask-number ()
;;   (format t "Please enter a number. ")
;;   (let ((val (read)))
;;     (if (numberp val)
;; 	val
;; 	(ask-number))))

;; (ask-number)


;;; global variable
;; (defparameter *glob* 99)
;; (defconstant limit (+ *glob* 1))

;; (boundp '*glob*)

;;; assignment
;; (setf *glob* 98)

;; (let ((n 10))
;;   (setf n 2)
;;   n)

;; (setf x '(a b c))

;; (setf a 'a
;;       b 'b
;;       c 'c)

;;; functional programming
;; (setf lst '(c a r a t))
;; (remove 'a lst)
;; lst

;; (setf x (remove 'a x))
;; x

;;; iteration
(defun show-squares (start end)
  (do ((i start (+ i 1)))
      ((> i end) 'done)
    (format t "~A ~A~%" i (* i i))))

(show-squares 2 5)
; recursive version
(defun show-squares2 (i end)
  (if (> i end)
      'done
      (progn
	(format t "~A ~A~%" i (* i i))
	(show-squares2 (+ i 1) end))))

(show-squares2 2 5)
       
(defun our-length (lst)
  (let ((len 0))
    (dolist (obj lst)
      (setf len (+ len 1)))
    len))

(our-length '(a b c d))
; recursive version
(defun our-length2 (lst)
  (if (null lst)
      0
      (+ (our-length2 (cdr lst)) 1)))

(our-length2 '(a b c d))


;;; function as objects

(function +)
#'-
(apply #'+ '(1 2 3))
(funcall #'+ 1 2 3)

((lambda (x) (+ x 100)) 1)
(funcall #'(lambda (x) (+ x 100)) 1)


;;; types
(typep 27 'integer)
