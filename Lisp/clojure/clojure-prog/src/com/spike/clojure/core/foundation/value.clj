(ns com.spike.clojure.core.foundation.value)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; 值: 函数式数据结构 不可变和高效的
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(def h {[1 2] 3})                      ; map的key为vector
(h [1 2])                              ; vector本身作为函数
(conj (first (keys h)) 3)              ; [1 2 3]
; 保持不变
(h [1 2])
h