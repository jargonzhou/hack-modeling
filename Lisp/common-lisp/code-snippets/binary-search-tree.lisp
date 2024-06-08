;;;; 二叉查找树

(in-package :com.spike.language.cl.snippets)

;;; 节点定义
(defstruct (node (:print-function
		  (lambda (n s d)
		    (format s "#<~A>" (node-elt n)))))
  ;; 元素
  elt
  ;; 左子树
  (l nil)
  ;; 右子树
  (r nil))

;;; 插入
(defun bst-insert (obj bst <)
  (if (null bst)
      (make-node :elt obj)
      (let ((elt (node-elt bst)))
	(if (eql obj elt)
	    bst
	    (if (funcall < obj elt)
		;; 当前节点较大: 插入左子树
		(make-node :elt elt
			   :l (bst-insert obj (node-l bst) <)
			   :r (node-r bst))
		(make-node :elt elt
			   :r (bst-insert obj (node-r bst) <)
			   :l (node-l bst)))))))

;;; 查找
(defun bst-find (obj bst <)
  (if (null bst)
      nil
      (let ((elt (node-elt bst)))
	(if (eql obj elt)
	    bst
	    (if (funcall < obj elt)
		;; 当前节点较大: 在左子树中查找
		(bst-find obj (node-l bst) <)
		(bst-find obj (node-r bst) <))))))

(defun bst-min (bst)
  (and bst
       (or (bst-min (node-l bst)) bst)))

(defun bst-max (bst)
  (and bst
       (or (bst-max (node-r bst)) bst)))

;;; 删除
(defun bst-remove (obj bst <)
  (if (null bst)
      nil
      (let ((elt (node-elt bst)))
	(if (eql obj elt)
	    (percolate bst) ;找到节点
	    (if (funcall < obj elt)
		;; 当前节点较大: 在左子树中删除
		(make-node :elt elt
			   :l (bst-remove obj (node-l bst) <)
			   :r (node-r bst))
		(make-node :elt elt
			   :r (bst-remove obj (node-r bst) <)
			   :l (node-l bst)))))))

(defun percolate (bst)
  (cond ((null (node-l bst))                ;左子树为空
	 (if (null (node-r bst))
	     nil
	     (rperc bst)))
	((null (node-r bst)) (lperc bst))   ;右子树为空
	(t (if (zerop (random 2))           ;左右子树均不为空
	       (lperc bst)
	       (rperc bst)))))

(defun rperc (bst)
  (make-node :elt (node-elt (node-r bst))
	     :l (node-l bst)
	     :r (percolate (node-r bst))))

(defun lperc (bst)
  (make-node :elt (node-elt (node-l bst))
	     :l (percolate (node-l bst))
	     :r (node-r bst)))


;;; 遍历
(defun bst-traverse (fn bst)
  (when bst
    (bst-traverse fn (node-l bst))
    (funcall fn (node-elt bst))
    (bst-traverse fn (node-r bst))))


;;; tests
(let ((nums nil))
  (dolist (x '(5 8 4 2 1 9 6 7 3))
    (setf nums (bst-insert x nums #'<)))
  (print nums)
  (bst-traverse #'princ nums)
  (print (list
	  (bst-find 12 nums #'<)
	  (bst-find 4 nums #'<)
	  (bst-min nums)
	  (bst-max nums)))
  (setf nums (bst-remove 2 nums #'<))
  (print (bst-find 2 nums #'<))
  (bst-traverse #'princ nums))




