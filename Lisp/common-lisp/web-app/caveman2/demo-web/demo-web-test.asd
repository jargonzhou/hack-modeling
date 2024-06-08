(defsystem "demo-web-test"
  :defsystem-depends-on ("prove-asdf")
  :author "zhoujiagen"
  :license ""
  :depends-on ("demo-web"
               "prove")
  :components ((:module "tests"
                :components
                ((:test-file "demo-web"))))
  :description "Test system for demo-web"
  :perform (test-op (op c) (symbol-call :prove-asdf :run-test-system c)))
