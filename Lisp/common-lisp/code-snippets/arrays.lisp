;;;; 数组

; 创建
(setf arr (make-array '(2 3) :initial-element nil))
; 访问
(aref arr 0 0)
(setf (aref arr 0 0) 'b)
(aref arr 0 0)

(setf *print-array* t)
(list arr)


;;; 向量: 一维数组
(setf vec (make-array 4 :initial-element nil))
(vector "a" 'b 3)
; 访问
(svref vec 0) ; sv: simple vector



      
