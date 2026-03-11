# ParEdit
* https://www.emacswiki.org/emacs/ParEdit

> ParEdit (`paredit.el`) is a minor mode for performing structured editing of S-expression data.

```
M-x package-install RET paredit RET
```

use with Emacs's Lips modes: `~/.emacs`
```lisp
(autoload 'enable-paredit-mode "paredit" "Turn on pseudo-structural editing of Lisp code." t)
(add-hook 'emacs-lisp-mode-hook       #'enable-paredit-mode)
(add-hook 'eval-expression-minibuffer-setup-hook #'enable-paredit-mode)
(add-hook 'ielm-mode-hook             #'enable-paredit-mode)
(add-hook 'lisp-mode-hook             #'enable-paredit-mode)
(add-hook 'lisp-interaction-mode-hook #'enable-paredit-mode)
(add-hook 'scheme-mode-hook           #'enable-paredit-mode)
```