(defun addn (n)
  #'(lambda (x)
      (+ n x)))

(addn 1)
(funcall (addn 1) 2)
(apply (addn 1) '(2)) 
