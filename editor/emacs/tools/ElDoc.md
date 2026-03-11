# ElDoc
* https://www.emacswiki.org/emacs/ElDoc

> A very simple but effective thing, eldoc-mode is a [MinorMode](https://www.emacswiki.org/emacs/MinorMode) which shows you, in the echo area, the argument list of the function call you are currently writing. Very handy. By [NoahFriedman](https://www.emacswiki.org/emacs/NoahFriedman). Part of Emacs.

```lisp
; ~/.emacs
(add-hook 'emacs-lisp-mode-hook 'eldoc-mode)
(add-hook 'lisp-interaction-mode-hook 'eldoc-mode)
(add-hook 'ielm-mode-hook 'eldoc-mode)
```