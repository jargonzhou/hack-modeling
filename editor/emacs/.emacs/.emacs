(require 'package)
;; Add the MELPA archive to the list of package archives
(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/") t)

(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(ac-use-quick-help t)
 '(debug-on-error t)
 '(eww-search-prefix "file://")
 '(package-selected-packages
   '(org pdf-tools ac-slime slime yasnippet projectile-codesearch paredit cl-libify auto-complete markdown-mode treemacs-tab-bar treemacs-persp treemacs-magit treemacs-icons-dired treemacs-projectile treemacs-evil treemacs slime-volleyball solarized-theme))
 '(treemacs-python-executable "D:/software/miniconda3/python.exe"))

;;; reload configuration file
(defun reload-user-init-file ()
  "Reload your .emacs file without restarting Emacs."
  (interactive)
  (load-file user-init-file))

;;; fonts
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 ;'(default ((t (:inherit nil :extend nil :stipple nil :background "#fdf6e3" :foreground "#657b83" :inverse-video nil :box nil :strike-through nil :overline nil :underline nil :slant normal :weight medium :height 120 :width normal :foundry "outline" :family "JetBrains Mono"))))
 '(default ((t (:family "JetBrains Mono" :foundry "JB" :slant normal :weight regular :height 110 :width normal)))))

(global-font-lock-mode t)

;;; EWW
(setq browse-url-browser-function 'eww-browse-url)

;;; SHELL
(setq explicit-shell-file-name "C:/Program Files/Git/bin/bash.exe")

;;; SLIME
;(load (expand-file-name "C:/Users/zhouj/quicklisp/slime-helper.el"))
(dolist (package '(slime))
  (unless (package-installed-p package)
    (package-install package)))
(require 'slime)
(slime-setup '(slime-fancy slime-quicklisp slime-asdf slime-mrepl slime-xref-browser slime-highlight-edits))
(setq inferior-lisp-program "D:/software/SBCL-2.6.0/sbcl.exe"
  common-lisp-hyperspec-root "file:///D:/document/RTFD/lisp/HyperSpec-7-0/HyperSpec/"
  common-lisp-hyperspec-symbol-table "file:///D:/document/RTFD/lisp/HyperSpec-7-0/HyperSpec/Data/Map_Sym.txt")
; highlight edit content
(slime-highlight-edits-mode 1)

;;; full screen
(add-hook 'window-setup-hook 'toggle-frame-maximized t)
;;; https://emacs.stackexchange.com/questions/2999/how-to-maximize-my-emacs-frame-on-start-up
; (add-to-list 'initial-frame-alist '(fullscreen . maximized))

;;; menubar, toolbar, scrollbar
;;; https://kb.mit.edu/confluence/display/istcontrib/Disabling+the+Emacs+menubar%2C+toolbar%2C+or+scrollbar
;;; https://www.gnu.org/software/emacs/manual/html_node/emacs/Frames.html
(menu-bar-mode 1)
(tool-bar-mode -1)
(scroll-bar-mode -1)

;;; line number
(global-display-line-numbers-mode 1)

;;; encoding
(set-default-coding-systems 'unix)
(set-buffer-file-coding-system 'unix)
(set-terminal-coding-system 'unix)

;;; theme
(load-theme 'zenburn t)

;;; game
;;; https://www.gnu.org/software/emacs/manual/html_node/emacs/Amusements.html

;;; Fast minibuffer selection
;;; https://www.gnu.org/software/emacs/manual/html_node/emacs/Icomplete.html
(fido-mode t)

;;; Calendar
(setq calendar-week-start-day 1)

;;; auto complete
(ac-config-default)
(set-face-background 'ac-candidate-face "lightgray")
(set-face-underline 'ac-candidate-face "darkgray")
(set-face-background 'ac-selection-face "steelblue")
;;; ac-slime
(add-hook 'slime-mode-hook 'set-up-slime-ac)
(add-hook 'slime-repl-mode-hook 'set-up-slime-ac)
(eval-after-load "auto-complete"
                 '(add-to-list 'ac-modes 'slime-repl-mode))

;;; log4cl
;;;(load "C:/Users/zhouj/quicklisp/log4slime-setup.el")
;;;(global-log4slime-mode 1)

;;; YASnippet
(yas-global-mode 1)

;;; prevent backup files
; bash: find . -name '*~' -delete
(setq make-backup-files nil)

;;; ParEdit
(autoload 'enable-paredit-mode "paredit" "Turn on pseudo-structural editing of Lisp code." t)
(add-hook 'emacs-lisp-mode-hook #'enable-paredit-mode)
(add-hook 'eval-expression-minibuffer-setup-hook #'enable-paredit-mode)
(add-hook 'ielm-mode-hook #'enable-paredit-mode)
(add-hook 'lisp-mode-hook #'enable-paredit-mode)
(add-hook 'lisp-interaction-mode-hook #'enable-paredit-mode)
(add-hook 'scheme-mode-hook #'enable-paredit-mode)

;;; Projectile 
(projectile-mode +1)
;; Recommended keymap prefix on macOS
; (define-key projectile-mode-map (kbd "s-p") 'projectile-command-map)
;; Recommended keymap prefix on Windows/Linux
(define-key projectile-mode-map (kbd "C-c p") 'projectile-command-map)


;;; treemacs
(use-package treemacs
             :ensure t
             :defer t
             :init
             (with-eval-after-load 'winum
                                   (define-key winum-keymap (kbd "M-0") #'treemacs-select-window))
             :config
             (progn
              ; (setq treemacs-python-executable "D:/software/miniconda3/python.exe")

              (setq treemacs-buffer-name-function #'treemacs-default-buffer-name
                treemacs-buffer-name-prefix " *Treemacs-Buffer-"
                treemacs-collapse-dirs (if treemacs-python-executable 3 0)
                treemacs-deferred-git-apply-delay 0.5
                treemacs-directory-name-transformer #'identity
                treemacs-display-in-side-window t
                treemacs-eldoc-display 'simple
                treemacs-file-event-delay 2000
                treemacs-file-extension-regex treemacs-last-period-regex-value
                treemacs-file-follow-delay 0.2
                treemacs-file-name-transformer #'identity
                treemacs-follow-after-init t
                treemacs-expand-after-init t
                treemacs-find-workspace-method 'find-for-file-or-pick-first
                treemacs-git-command-pipe ""
                treemacs-goto-tag-strategy 'refetch-index
                treemacs-header-scroll-indicators '(nil . "^^^^^^")
                treemacs-hide-dot-git-directory t
                treemacs-hide-dot-jj-directory t
                treemacs-indentation 2
                treemacs-indentation-string " "
                treemacs-is-never-other-window nil
                treemacs-max-git-entries 5000
                treemacs-missing-project-action 'ask
                treemacs-move-files-by-mouse-dragging t
                treemacs-move-forward-on-expand nil
                treemacs-no-png-images nil
                treemacs-no-delete-other-windows t
                treemacs-project-follow-cleanup nil
                treemacs-persist-file (expand-file-name ".cache/treemacs-persist" user-emacs-directory)
                treemacs-position 'left
                treemacs-read-string-input 'from-child-frame
                treemacs-recenter-distance 0.1
                treemacs-recenter-after-file-follow nil
                treemacs-recenter-after-tag-follow nil
                treemacs-recenter-after-project-jump 'always
                treemacs-recenter-after-project-expand 'on-distance
                treemacs-litter-directories '("/node_modules" "/.venv" "/.cask")
                treemacs-project-follow-into-home nil
                treemacs-show-cursor nil
                treemacs-show-hidden-files t
                treemacs-silent-filewatch nil
                treemacs-silent-refresh nil
                treemacs-sorting 'alphabetic-asc
                treemacs-select-when-already-in-treemacs 'move-back
                treemacs-space-between-root-nodes t
                treemacs-tag-follow-cleanup t
                treemacs-tag-follow-delay 1.5
                treemacs-text-scale nil
                treemacs-user-mode-line-format nil
                treemacs-user-header-line-format nil
                treemacs-wide-toggle-width 70
                treemacs-width 35
                treemacs-width-increment 1
                treemacs-width-is-initially-locked t
                treemacs-workspace-switch-cleanup nil)

              ;; The default width and height of the icons is 22 pixels. If you are
              ;; using a Hi-DPI display, uncomment this to double the icon size.
              ;;(treemacs-resize-icons 44)

              (treemacs-follow-mode t)
              (treemacs-filewatch-mode t)
              (treemacs-fringe-indicator-mode 'always)
              (when treemacs-python-executable
                    (treemacs-git-commit-diff-mode t))

              (pcase (cons (not (null (executable-find "git")))
                           (not (null treemacs-python-executable)))
                     (`(t . t)
                       (treemacs-git-mode 'deferred))
                     (`(t . _)
                       (treemacs-git-mode 'simple)))

              (treemacs-hide-gitignored-files-mode nil))
             :bind
             (:map global-map
                   ("M-0" . treemacs-select-window)
                   ("C-x t 1" . treemacs-delete-other-windows)
                   ("C-x t t" . treemacs)
                   ("C-x t d" . treemacs-select-directory)
                   ("C-x t B" . treemacs-bookmark)
                   ("C-x t C-t" . treemacs-find-file)
                   ("C-x t M-t" . treemacs-find-tag)))

(use-package treemacs-evil
             :after (treemacs evil)
             :ensure t)

(use-package treemacs-projectile
             :after (treemacs projectile)
             :ensure t)

(use-package treemacs-icons-dired
             :hook (dired-mode . treemacs-icons-dired-enable-once)
             :ensure t)

(use-package treemacs-magit
             :after (treemacs magit)
             :ensure t)

(use-package treemacs-persp ;;treemacs-perspective if you use perspective.el vs. persp-mode
             :after (treemacs persp-mode) ;;or perspective vs. persp-mode
             :ensure t
             :config (treemacs-set-scope-type 'Perspectives))

(use-package treemacs-tab-bar ;;treemacs-tab-bar if you use tab-bar-mode
             :after (treemacs)
             :ensure t
             :config (treemacs-set-scope-type 'Tabs))

(treemacs-start-on-boot)
