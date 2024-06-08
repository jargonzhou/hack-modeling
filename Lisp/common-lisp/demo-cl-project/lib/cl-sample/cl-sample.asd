(defsystem "cl-sample"
  :version "0.1.0"
  :author "Eitaro Fukamachi"
  :license "LLGPL"
  :depends-on ("clack"
               "cl-annot")
  :components ((:module "src"
                :components
                ((:file "main"))))
  :description ""
  :in-order-to ((test-op (test-op "cl-sample/tests"))))

(defsystem "cl-sample/tests"
  :author "Eitaro Fukamachi"
  :license "LLGPL"
  :depends-on ("cl-sample"
               "rove")
  :components ((:module "tests"
                :components
                ((:file "main"))))
  :description "Test system for cl-sample"
  :perform (test-op (op c) (symbol-call :rove :run c)))
