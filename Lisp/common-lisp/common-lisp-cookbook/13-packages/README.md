# Packages

- [Creating a package](./my-package/test-package.lisp)

```lisp
✗ rlwrap sbcl
* (load "test-package.lisp")
T
* (in-package :my-package)
#<PACKAGE "MY-PACKAGE">
* (hello)

"Hello from my package." 
"Hello from my package."
* (in-package :cl-user)
#<PACKAGE "COMMON-LISP-USER">
* (my-package::hello)

"Hello from my package." 
"Hello from my package."
```
