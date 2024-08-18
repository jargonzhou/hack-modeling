(defpackage :com.spike.cl.demo-system
  (:use :asdf :cl))
(in-package :com.spike.cl.demo-system)

(defsystem demo
  :name "demo"
  :author "zhoujiagen"
  :version "1.0"
  :maintainer "zhoujiagen"
  :licence "MIT"
  :description "<description>"
  :long-description "<long-description>"
  :components
  ((:file "packages")
   (:file "demo" :depends-on ("packages"))))
