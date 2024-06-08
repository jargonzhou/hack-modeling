(in-package :com.spike.language.cl.snippets)

;;; conses
;(setf x (cons 'a nil))
;(setf y (list 'a 'b 'c))
;(cdr y)
; 嵌套列表
;(setf z (list 'a (list 'b 'c ) 'd))
;(car (cdr z))

(defun our-listp (x)
  (or (null x) (consp x)))
(defun our-atom (x) (not (consp x)))


;;; 等价性
(eql (cons 'a nil) (cons 'a nil))

;(setf x (cons 'a nil))
;(eql x x)

;(equal x (cons 'a nil))

(defun our-equal (x y)
  (or (eql x y)
      (and (consp x)
	   (consp y)
	   (our-equal (car x) (car y))
	   (our-equal (cdr x) (cdr y)))))

;;; 为什么Lisp没有指针
;(setf x '(a b c))
;(setf y x)
;(eql x y)


;;; 构建列表
;(setf x '(a b c)
;      y (copy-list x))

(defun our-copy-list (lst)
  (if (atom lst)
      lst
      (cons (car lst) (our-copy-list (cdr lst)))))

(append '(a b) '(c d) '(e))


;;; 访问
(nth 0 '(a b c))
(nthcdr 2 '(a b c))

(defun our-nthcdr (n lst)
  (if (zerop n)
      lst
      (our-nthcdr (- n 1) (cdr lst))))
(our-nthcdr 2 '(a b c))

(last '(a b c d))

;;; 映射函数

(mapcar #'(lambda (x) (+ x 10))
	'(1 2 3))
(mapcar #'list
	'(a b c)
	'(1 2 3 4))
; 调用列表的cdrs
(maplist #'(lambda (x) x)
	 '(a b c))

;;; 树
(defun our-copy-tree (tr)
  (if (atom tr)
      tr
      (cons (our-copy-tree (car tr))
	    (our-copy-tree (cdr tr)))))

(our-copy-tree '(a (b c) d))

; on sequence
(substitute 'y 'x '(and (integerp x) (zerop (mod x 2))))
; on tree
(subst 'y 'x '(and (integerp x) (zerop (mod x 2))))

(defun our-subst (new old tree)
  (if (eql tree old)
      new
      (if (atom tree)
	  tree
	  (cons (our-subst new old (car tree))
		(our-subst new old (cdr tree))))))


;;; 理解递归

(defun len (lst)
  (if (null lst)
      0
      (+ (len (cdr lst)) 1)))
(len '(1 2 3 4 5))

(defun our-member (obj lst)
  (if (eql (car lst) obj)
      lst
      (our-member obj (cdr lst))))
(our-member '1 '(1 2 3))

;;; 集

(member 'b '(a b c))
(member '(a) '((a) (z)) :test #'equal)
(member 'a '((a b) (c d)) :key #'car)
(member-if #'oddp '(2 3 4))

(defun our-member-if (fn lst)
  (and (consp lst)
       (if (funcall fn (car lst))
	   lst
	   (our-member-if fn (cdr lst)))))

(adjoin 'b '(a b c))
(adjoin 'z '(a b c))

(union '(a b c) '(c b s))
(intersection '(a b c) '(b b c))
(set-difference '(a b c d e) '(d e))

;;; 序列
(length '(a b c))
; 获取子序列
(subseq '(a b c d) 1 2)
(subseq '(a b c d) 1)
; 翻转
(reverse '(a b c))

(defun mirror-p (s)
  (if (eql 1 (length s))
      t
      (let ((len (length s)))
	(if (evenp len)
	    (let ((mid (/ len 2)))
	      (equal (subseq s 0 mid)
		     (reverse (subseq s mid))))
	    (let ((mid (/ (- len 1) 2)))
	      (equal (subseq s 0 mid)
		     (reverse (subseq s (+ mid 1)))))))))

(mirror-p '(1))
(mirror-p '(1 2 1))
(mirror-p '(1 2 2 1))

; 排序
(sort '(0 2 1 3 8) #'>)

(defun nth-most (n lst)
  (nth (- n 1)
       (sort (copy-list lst) #'>)))

(nth-most 2 '(0 2 1 3 8))

; every, some
(every #'oddp '(1 3 5))
(some #'oddp '(1 3 5))

(every #'> '(1 3 5) '(0 2 4))

;;; 栈
;(setf x '(b))
;(push 'a x)
;(setf y x)
;(pop x)
;(list x y) ; ((B) (A B))

(defun our-reverse (lst)
  (let ((acc nil))
    (dolist (elt lst)
      (push elt acc))
    acc))

(our-reverse '(1 2 3))

; pushnew use adjoin
(let ((x '(a b)))
  (pushnew 'c x)
  (pushnew 'a x)
  x)

;;; 点列表
(defun proper-list-p (x)
  (or (null x)
      (and (consp x)
	   (proper-list-p (cdr x)))))

(proper-list-p '(1 2))
(proper-list-p '(1 (2 3) 4))
(proper-list-p (cons 'a 'b))

;(setf pair (cons 'a 'b))
'(a . (b . (c . nil)))
(cons 'a (cons 'b (cons 'c 'd)))

; (a b)的等价形式
'(a . (b . nil))
'(a . (b))
'(a b . nil)
'(a b)

;;; 关联列表: cons的列表
;(setf trans '((+ . "add") (- . "subtract")))

;(assoc '+ trans)
;(assoc '* trans)

(defun our-assoc (key alist)
  (and (consp alist)
       (let ((pair (car alist)))
	 (if (eql key (car pair))
	     pair
	     (our-assoc key (cdr alist))))))

;(our-assoc '+ trans)
;(our-assoc '* trans)
