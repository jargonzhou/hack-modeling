# Common Lisp

- ASDF配置

```shell
$ mkdir -p ~/.config/common-lisp/source-registry.conf.d/
$ cd ~/.config/common-lisp/source-registry.conf.d/
$ touch playground.conf
$ vi playground.conf
(:tree "<.../CommonLisp-playground/>“)

.../CommonLisp-playground/email-db
├── email-db.asd
├── email-db.lisp
└── packages.lisp
```

- email-db.lisp

```lisp
(in-package :com.spike.language.cl.email-db)
(defun hello-world ()
  (write-line "hello, email-db"))
```

- packages.lisp

```lisp
(in-package :common-lisp-user)
(defpackage :com.spike.language.cl.email-db
  (:use :common-lisp)
  (:export :hello-world))
```  

- email-db.asd

```lisp
(defpackage :com.spike.language.cl.email-db-system (:use :asdf :cl))
(in-package :com.spike.language.cl.email-db-system)
(defsystem email-db
  :name "email-db"
  :author "<Author>"
  :version "1.0"
  :maintainer "<maintainer>"
  :licence "<licence>"
  :description "<description>"
  :long-description "<long-description>"
  :components
  ((:file "packages")
   (:file "email-db" :depends-on ("packages"))))
```

- 运行

```shell
$ sbcl

* (require :asdf)
* (asdf:load-system :email-db)

* (in-package :com.spike.language.cl.email-db)
#<PACKAGE "COM.SPIKE.LANGUAGE.CL.EMAIL-DB">
* (hello-world)
hello, email-db
"hello, email-db"
```
