# 3 Practical: A Simple Database

```shell
mkdir -p ~/.config/common-lisp/source-registry.conf.d/
CURRENT_DIR=`pwd`
SYSTEM_NAME=simple-file-db
echo '(:tree "'$CURRENT_DIR'/")' > ~/.config/common-lisp/source-registry.conf.d/$SYSTEM_NAME.conf
```

```lisp
✗ rlwrap sbcl 
* (asdf:load-system "simple-file-db")
* (in-package :com.spike.cl.simple-file-db)
#<PACKAGE "COM.SPIKE.CL.SIMPLE-FILE-DB">
* (info)
hello, simple-file-db
"hello, simple-file-db"
```
