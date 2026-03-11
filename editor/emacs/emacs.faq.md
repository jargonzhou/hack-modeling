# GNU Emacs FAQ
* https://www.gnu.org/software/emacs/manual/efaq.html

# Mode

* [Retrieve all the major modes equipped with emacs](https://emacs.stackexchange.com/questions/51540/retrieve-all-the-major-modes-equipped-with-emacs)
```
# grep 'define-derived-mode' macro in 'emacs-source/lisp'
grep -A 1 '(define-derived-mode' **/*.el

# 'built-in' status by
M-x package-list-packages

# variable: auto-mode-alist
# `lisp/files.el` 
C-h auto-mode-alist
```

# As a Work Environment
* [How to find a file in Emacs without known exact directory?](https://stackoverflow.com/questions/4340949/how-to-find-a-file-in-emacs-without-known-exact-directory)
```
# prompted for root directory to search with a file mask
M-x find-name-dired
```

# Configuration
## Font
* [Set Fonts](https://www.emacswiki.org/emacs/SetFonts)
* [stackoverflow: How to set the font size in Emacs?](https://stackoverflow.com/questions/294664/how-to-set-the-font-size-in-emacs)
```shell
# check font backend
M-: (frame-parameter nil 'font-backend) RET
# output (x): use old X font facilities
# fix: lib `libxft-dev`, --with-xft

M-x customize-face RET default
```
## Line Number
```lisp
;;; global line number
;;; https://www.gnu.org/software/emacs/manual/html_node/efaq/Displaying-the-current-line-or-column.html
;;; https://www.emacswiki.org/emacs/LineNumbers
;;; (setq column-number-mode t)
(global-display-line-numbers-mode 1)
```

## Character Encoding
* [Emac Language Environment](https://www.emacswiki.org/emacs/LanguageEnvironment)

``` lisp
(set-terminal-coding-system 'utf-8)
(set-default-coding-systems 'utf-8)
```

REF: https://codeday.me/bug/20190303/737251.html
``` shell
# SBCL
LC_CTYPE=en_US.UTF-8
export LC_CTYPE
```

``` lisp
; SLIME 2.22
CL-USER> sb-impl::*default-external-format*
:US-ASCII
CL-USER> (setf sb-impl::*default-external-format* :UTF-8)
:UTF-8
CL-USER> sb-impl::*default-external-format*
:UTF-8
```
or in `~/.sbclrc`:

``` lisp
;;; set external format
(setf sb-impl::*default-external-format* :UTF-8)
```