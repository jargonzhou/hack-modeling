;;; counter的简单测试
(in-package :com.spike.cl.ansi-cl.ctr)

(let ((c (make-instance 'counter)))
  (format t "~A~%" (slot-value c 'state))
  (increment c)
  (increment c)
  (format t "~A~%" (slot-value c 'state))
  (clear c)
  (format t "~A~%" (slot-value c 'state)))
