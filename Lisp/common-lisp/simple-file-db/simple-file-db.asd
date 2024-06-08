(defpackage :com.spike.language.cl.simple-file-db-system (:use :asdf :cl))
(in-package :com.spike.language.cl.simple-file-db-system)

(defsystem simple-file-db
  :name "simple-file-db"
  :author "<Author>"
  :version "1.0"
  :maintainer "<maintainer>"
  :licence "<licence>"
  :description "简单的基于文本的CD数据库"
  :long-description "<long-description>"
  :components
  ((:file "packages")
   (:file "simple-file-db" :depends-on ("packages"))))
