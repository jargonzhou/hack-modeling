;;;; 状况

(error "Your report use ~A as a verb." 'status)

(ecase 1 (2 3) (4 5))

(let ((x '(a b c)))
  (check-type (car x) integer "an integer")
  x)

(let ((sandwich '(ham on rye)))
  (assert (eql (car sandwich) 'chicken)
	  ((car sandwich))
	  "I wanted a ~A sandwich." 'chicken)
  sandwich)
