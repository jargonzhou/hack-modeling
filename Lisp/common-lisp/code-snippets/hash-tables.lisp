;;;; 哈希表

(in-package :com.spike.language.cl.snippets)

(let ((ht (make-hash-table)))
  (print (gethash 'color ht))
  (setf (gethash 'color ht) 'red)
  (print (gethash 'color ht)))

;;; 键和值可以是任意类型的对象
;;; key: funtion, values: strings
(let ((bugs (make-hash-table)))
  (push "Doesn't take keyword arguments."
	(gethash #'our-member bugs)))


;;; 使用哈希表表示集合
(let ((fruit (make-hash-table)))
  (setf (gethash 'apricot fruit) t)
  (print (gethash 'apricot fruit))
  ;; 删除元素: remhash
  (remhash 'apricot fruit)
  (gethash 'apricot fruit))


;;; 迭代: maphash

(let ((ht (make-hash-table)))
  (setf (gethash 'shape ht) 'spherical
	(gethash 'size ht) 'giant)
  (maphash #'(lambda (k v)
	       (format t "~A = ~A~%" k v))
	   ht))
	   

(defun print-hash-table (ht)
  (maphash #'(lambda (k v)
	       (format t "~A = ~A~%" k v)) ht ))

(print-hash-table (make-hash-table))
(let ((ht (make-hash-table)))
  (setf (gethash 'a ht) t)
  (print-hash-table ht))

;;; 一些可用的关键字参数
(let ((ht (make-hash-table :size 5 :test #'equal)))
  (print ht))
