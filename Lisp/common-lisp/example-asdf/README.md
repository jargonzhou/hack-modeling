# ASDF

Load `demo` system:

```shell
✗ CURRENT_DIR=`pwd`       
✗ SYSTEM_NAME=demo
✗ echo '(:tree "'$CURRENT_DIR'/")' > ~/.config/common-lisp/source-registry.conf.d/$SYSTEM_NAME.conf
```

```lisp
✗ rlwrap sbcl 
* (asdf:load-system :demo)
* (in-package :com.spike.cl.demo)
#<PACKAGE "COM.SPIKE.CL.DEMO">
* (hello-world)
hello, demo
"hello, demo"
```