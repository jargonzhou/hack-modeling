;;;; 最短路径
;;;; ANSI Common Lisp P.51
;;;;
;;;; 节点用符号标识, 网络用元素为(node . neighbors)的关联列表表示

; a -> b, a -> c
; b -> c
; c -> d
(setf min-net '((a b c) (b c) (c d)))
(cdr (assoc 'a min-net)) ;(B C)


(defun shorteset-path (start end net)
  (bfs end (list (list start)) net)) ;组装队列: ((start))

(defun bfs (end queue net)
  (format t "Queue: ~A~%" queue)
  (if (null queue)
      nil
      (let ((path (car queue))) ;首个路径队列
	(let ((node (car path)));路径中最后遍历的节点
	  (if (eql node end)    ;是否遇到终止节点
	      (reverse path)
	      (bfs end
		   ;; 队列中后面的路径, 该节点可达路径
		   (append (cdr queue) (new-paths path node net))
		   net))))))


(defun new-paths (path node net)
  (format t "  Path: ~A, node: ~A~%" path node)
  (mapcar #'(lambda (n)
	      (cons n path))
	  ;; node可达的节点列表
	  (cdr (assoc node net))))

(shorteset-path 'a 'd min-net)

;; Queue: ((A))
;;   Path: (A), node: A
;; Queue: ((B A) (C A))
;;   Path: (B A), node: B
;; Queue: ((C A) (C B A))
;;   Path: (C A), node: C
;; Queue: ((C B A) (D C A))
;;   Path: (C B A), node: C
;; Queue: ((D C A) (D C B A))

;; (A C D)

