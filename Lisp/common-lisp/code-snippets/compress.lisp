;;;; run-length encoding
;;;;
;;;; example:
;;;; > (compress '(1 1 1 0 1 0 0 0 0 1))
;;;; ((3 1) 0 1 (4 0) 1)
;;;;
;;;; > (uncompress '((3 1) 0 1 (4 0) 1))
;;;; (1 1 1 0 1 0 0 0 0 1)

;;; 压缩
(defun compress (x)
  ;; 如果不是cons直接返回
  (if (consp x)
      (compr (car x) 1 (cdr x))
      x))

;;; elt出现了n次, 继续在lst中压缩
(defun compr (elt n lst)
  (if (null lst)
      (list (n-elts elt n))
      ;; 这里lst非空
      (let ((next (car lst))) ;取lst中下一个元素
	(if (eql next elt)
	    (compr elt (+ n 1) (cdr lst))
	    (cons (n-elts elt n)
		  (compr next 1 (cdr lst)))))))

;;; 返回: (n elt) 或 elt
(defun n-elts (elt n)
  (if (> n 1)
      (list n elt)
      elt))


(compress '(1 1 1 0 1 0 0 0 0 1))


;;; 解压
(defun uncompress (lst)
  (if (null lst)
      nil
      ;; 这里lst非空
      (let ((elt (car lst))
	    (rest (uncompress (cdr lst))))
	(if (consp elt) ; 如果elt是cons
	    (append (apply #'list-of elt)
		    rest)
	    (cons elt rest)))))

;;; 构造长度为n元素均为elt的列表
(defun list-of (n elt)
  (if (zerop n)
      nil
      (cons elt (list-of (- n 1) elt))))

(uncompress '((3 1) 0 1 (4 0) 1))



