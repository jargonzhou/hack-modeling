;;;; 序列

(in-package :com.spike.language.cl.snippets)

; 引用list.lisp中定义的函数
(mirror-p "abba")

; elt可用于任意序列
(elt '(a b c) 1)

; 序列函数的关键字参数: :key, :test, :from-end, :start, :end
(position #\a "fantasia")
(position #\a "fantasia" :start 3 :end 5)
(position #\a "fantasia" :from-end t)
(position 'a '((c d) (a b)) :key #'car)

(position '(a b) '((a b) (c d))) ; NIL
(position '(a b) '((a b) (c d)) :test #'equal) ; 0

(defun second-word (str)
  (let ((p1 (+ (position #\  str) 1)))
    (subseq str p1 (position #\  str :start p1))))

(let ((str "Frorm follows function."))
  (second-word str))

(position-if #'oddp '(2 3 4 5))

(find #\a "cat")

(find-if #'characterp "ham")

; 去重
(remove-duplicates "abracadabra")

; list to a single value
(reduce #'intersection '((b r a d 's) (b a d) (c a t)))
