;;;; 二分查找: 在已排序向量中查找

(defun bin-search (obj vec)
  (let ((len (length vec)))
    (and (not (zerop len))
	 (finder obj vec 0 (- len 1)))))

;;; 在向量的一个范围内查找
(defun finder (obj vec start end)
  (let ((range (- end start)))
    (if (zerop range)
	(if (eql obj (aref vec start))
	    obj
	    nil)
	(let ((mid (+ start (round (/ range 2)))))
	  (let ((obj2 (aref vec mid))) ; 范围中中间处的值
	    (if (< obj obj2)
		(finder obj vec start (- mid 1))
		(if (> obj obj2)
		    (finder obj vec (+ mid 1) end)
		    obj)))))))

(let ((vec (vector 1 2 3 4 5 6 7 8 9)))
  (values (bin-search 4 vec)
	  (bin-search 10 vec)))
