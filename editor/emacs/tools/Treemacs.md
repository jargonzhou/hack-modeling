# Treemacs
* https://github.com/Alexander-Miller/treemacs
* [Keymap](https://github.com/Alexander-Miller/treemacs?tab=readme-ov-file#keymap)

> Treemacs is a file and project explorer similar to NeoTree or vim’s NerdTree, but largely inspired by the Project Explorer in Eclipse. It shows the file system outlines of your projects in a simple tree layout allowing quick navigation and exploration, while also possessing **basic** file management utilities. Specifically a quick feature overview looks as follows:
>
>- **Project management**: Treemacs lets you view multiple file trees - projects - at once and quickly add or remove them, and groups projects in workspaces.
>- **Easy navigation**: quickly move between projects or use shortcuts to jump to parent or neighbouring nodes.
>- **Versatile file access**: decide exactly how and where a file will be opened, including using `ace-window` to choose a window or launching an external application.
>- **Understanding of frames**: every frame will receive its own treemacs buffer that will live and die with that frame.
>- **Finding of files and tags**: Treemacs can follow along and keep in focus the currently selected file or even the tag at point, either manually or automatically using either `treemacs-follow-mode` or `treemacs-tag-follow-mode`.
>- **Git Integration**: Treemacs can use different faces for files and directories based on their git status. The git process is run asynchronously, minimizing its performance impact.
>- **[Winum](https://github.com/deb0ch/emacs-winum) & [ace-window](https://github.com/abo-abo/ace-window) compatibility**: The presence of treemacs will not interfere with winum’s and ace-window’s usual layouts.
>- **[Projectile/project.el](https://github.com/bbatsov/projectile) integration**: the `treemacs-projectile` package lets you quickly add your projectile projects to the treemacs workspace. `project.el` compatibility is built-in.
>- **Simple mouse interface**: Left clicks will work the same as you’re used to from with graphical applications
>- **Session persistence**: Treemacs automatically saves and restores your workspaces.
>- **Dashing good looks**: Treemacs uses (optionally resizable) png images in HD 22x22 resolution for its icons. When run in a terminal a simple fallback is used.
>- **Tag view**: Treemacs can display files’ tags. All file types that Emacs can generate a (semantic) imenu index for are supported.
>- **Visual feedback**: When it would otherwise be difficult to see the message in the minibuffer success/failure is indicated with pulse.el.
>- **Theming support**: Treemacs supports using multiple icon themes that can be changed at will.
>- **Ease of use**: Treemacs offers many configuration options, but comes with a set of (what hopefully should be) sane defaults. Installation aside there are two obligatory pieces of setup: 1) Choosing convenient keybindings to run treemacs and 2) If you use evil: requiring `treemacs-evil` to integrate treemacs with evil and enable j/k navigation. More on both below. You can also summon helpful hydras with `?` and `C-?` that will remind you of treemacs’ many keybindings and features.
>- **Bookmark integration**: Running `bookmark-set` on a Treemacs item will store a bookmark to Treemacs buffer for that item.

# Installation
```
# see ~/.config/doom/init.el
M-x treemacs
```

```lisp
;;; Treemacs
(use-package treemacs
  :ensure t
  :defer t
  :init
  (with-eval-after-load 'winum
    (define-key winum-keymap (kbd "M-0") #'treemacs-select-window))
  :config
  (progn
    (setq treemacs-collapse-dirs                   (if treemacs-python-executable 3 0)
          treemacs-deferred-git-apply-delay        0.5
          treemacs-directory-name-transformer      #'identity
          treemacs-display-in-side-window          t
          treemacs-eldoc-display                   'simple
          treemacs-file-event-delay                2000
          treemacs-file-extension-regex            treemacs-last-period-regex-value
          treemacs-file-follow-delay               0.2
          treemacs-file-name-transformer           #'identity
          treemacs-follow-after-init               t
          treemacs-expand-after-init               t
          treemacs-find-workspace-method           'find-for-file-or-pick-first
          treemacs-git-command-pipe                ""
          treemacs-goto-tag-strategy               'refetch-index
          treemacs-header-scroll-indicators        '(nil . "^^^^^^")
          treemacs-hide-dot-git-directory          t
          treemacs-indentation                     2
          treemacs-indentation-string              " "
          treemacs-is-never-other-window           nil
          treemacs-max-git-entries                 5000
          treemacs-missing-project-action          'ask
          treemacs-move-files-by-mouse-dragging    t
          treemacs-move-forward-on-expand          nil
          treemacs-no-png-images                   nil
          treemacs-no-delete-other-windows         t
          treemacs-project-follow-cleanup          nil
          treemacs-persist-file                    (expand-file-name ".cache/treemacs-persist" user-emacs-directory)
          treemacs-position                        'left
          treemacs-read-string-input               'from-child-frame
          treemacs-recenter-distance               0.1
          treemacs-recenter-after-file-follow      nil
          treemacs-recenter-after-tag-follow       nil
          treemacs-recenter-after-project-jump     'always
          treemacs-recenter-after-project-expand   'on-distance
          treemacs-litter-directories              '("/node_modules" "/.venv" "/.cask")
          treemacs-project-follow-into-home        nil
          treemacs-show-cursor                     nil
          treemacs-show-hidden-files               t
          treemacs-silent-filewatch                nil
          treemacs-silent-refresh                  nil
          treemacs-sorting                         'alphabetic-asc
          treemacs-select-when-already-in-treemacs 'move-back
          treemacs-space-between-root-nodes        t
          treemacs-tag-follow-cleanup              t
          treemacs-tag-follow-delay                1.5
          treemacs-text-scale                      nil
          treemacs-user-mode-line-format           nil
          treemacs-user-header-line-format         nil
          treemacs-wide-toggle-width               70
          treemacs-width                           35
          treemacs-width-increment                 1
          treemacs-width-is-initially-locked       t
          treemacs-workspace-switch-cleanup        nil)

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
        ("M-0"       . treemacs-select-window)
        ("C-x t 1"   . treemacs-delete-other-windows)
        ("C-x t t"   . treemacs)
        ("C-x t d"   . treemacs-select-directory)
        ("C-x t B"   . treemacs-bookmark)
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
```

# Themes
- https://github.com/doomemacs/themes

- doom-solarized-light
- doom-zenburn

# Key Bindings

Workspace:
- `C-c C-w a`: create a new workspace
- `C-c C-w s`: switch the current workspace
- `C-c C-w d`: delete a workspace
- `C-c C-w f`: select the default fallback workspace
- `C-c C-w e`: Edit workspace layout via org-mode
	- `M-x treemacs-finish-edit`, `C-c C-c`


# FAQ
- [How to preview source file from treemacs in a project?](https://emacs.stackexchange.com/questions/74098/how-to-preview-source-file-from-treemacs-in-a-project)
Press `P` on treemacs sidebar: enable `treemacs-peek-mode`.