;;; MELPA
(require 'package)
(let* ((no-ssl (and (memq system-type '(windows-nt ms-dos))
                    (not (gnutls-available-p))))
       (proto (if no-ssl "http" "https")))
  ;; Comment/uncomment these two lines to enable/disable MELPA and MELPA Stable as desired
  (add-to-list 'package-archives (cons "melpa" (concat proto "://melpa.org/packages/")) t)
  ;;(add-to-list 'package-archives (cons "melpa-stable" (concat proto "://stable.melpa.org/packages/")) t)
  (when (< emacs-major-version 24)
    ;; For important compatibility libraries like cl-lib
    (add-to-list 'package-archives '("gnu" . (concat proto "://elpa.gnu.org/packages/")))))
(package-initialize)

;; Set your lisp system and, optionally, some contribs


(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(ecb-options-version "2.50")
 '(ecb-primary-secondary-mouse-buttons (quote mouse-1--mouse-2))
 '(package-selected-packages
   (quote
    (list-packages-ext ecb slime tagedit smex rainbow-delimiters projectile paredit magit javap-mode ido-ubiquitous exec-path-from-shell clojure-mode-extra-font-locking cider))))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(default ((t (:inherit nil :stipple nil :background "#292b2e" :foreground "#b2b2b2" :inverse-video nil :box nil :strike-through nil :overline nil :underline nil :slant normal :weight normal :height 150 :width normal :foundry "nil" :family "Ubuntu")))))

;;; global line number
(global-linum-mode t)

; bg-color, fg-color
; http://stackoverflow.com/questions/11418648/how-to-set-default-emacs-background-and-foreground-colors
; http://www.emacswiki.org/emacs/FrameParameters
;(add-to-list 'default-frame-alist '(foreground-color . "#000000"))
;(add-to-list 'default-frame-alist '(background-color . "#CCE8CC"))

;;; global line highlighting
;(global-hl-line-mode t) ;; To enable highlight line mode
;(set-face-background 'hl-line "#95d095")

;;; theme
(load-theme 'spacemacs-dark t)

;;; language environment
(set-language-environment "UTF-8")

;;; auto-complete
(ac-config-default)
; ac-slime
(require 'ac-slime)
(add-hook 'slime-mode-hook 'set-up-slime-ac)
 (add-hook 'slime-repl-mode-hook 'set-up-slime-ac)
 (eval-after-load "auto-complete"
   '(add-to-list 'ac-modes 'slime-repl-mode))

;;; activate ecb
(add-to-list 'load-path "/Users/zhoujiagen/.emacs.d/elpa/ecb-20170728.1921")
(load-file "/Users/zhoujiagen/.emacs.d/elpa/ecb-20170728.1921/ecb.el")
(require 'ecb)
;(require 'ecb-autoloads)
;(setq ecb-auto-activate t ecb-tip-of-the-day nil)
(setq ecb-tip-of-the-day nil)

;;; slime
(setq inferior-lisp-program "/usr/local/bin/sbcl")
(setq slime-contribs '(slime-fancy))

;;; erlang
;(setq load-path (cons  "/usr/local/Cellar/erlang/21.1.4/lib/erlang/lib/tools-3.0.1/emacs"
;      load-path))
;      (setq erlang-root-dir "/usr/local/Cellar/erlang/21.1.4")
;      (setq exec-path (cons "/usr/local/Cellar/erlang/21.1.4" exec-path))
;      (require 'erlang-start)
