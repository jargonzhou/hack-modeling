;;;; 字符串和字符

(sort "elbow" #'char<)

(aref "abc" 1)
(char "abc" 1)
(let ((str (copy-seq "Merlin")))
  (setf (char str 3) #\k)
  str)

; string-equal忽略大小写
(let ((a "fred")
      (b "Fred")
      (c "fred"))
  (values (equal a c)
    (equal a b)
    (string-equal a b)))

; format to nil
(format nil "~A or ~A" "truth" "dare")

