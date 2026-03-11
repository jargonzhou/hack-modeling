# Projectile
* https://github.com/bbatsov/projectile
* https://docs.projectile.mx/projectile/index.html

> **Projectile** is a project interaction library for Emacs. Its goal is to provide a nice set of features operating on a project level without introducing external dependencies (when feasible). For instance - finding project files has a portable implementation written in pure Emacs Lisp without the use of GNU `find` (but for performance sake an indexing mechanism backed by external commands exists as well).
>
> Projectile tries to be practical - portability is great, but if some external tools could speed up some task substantially and the tools are available, Projectile will leverage them.
>
> This library provides easy project management and navigation. The concept of a project is pretty basic - just a folder containing some special file (e.g. a VCS marker or a project descriptor file like `pom.xml` or `Gemfile`). Projectile will auto-detect pretty much every popular project type out of the box and you can easily extend it with additional project types.

```
M-x package-install RET projectile RET
```
```lisp
(projectile-mode +1)
;; Recommended keymap prefix on macOS
(define-key projectile-mode-map (kbd "s-p") 'projectile-command-map)
;; Recommended keymap prefix on Windows/Linux
(define-key projectile-mode-map (kbd "C-c p") 'projectile-command-map)
```

Enable `projectile-mode`, open a file in one of your projects and type a command such as `C-c p f`.

# extensions
* https://melpa.org/#/?q=projectile

# See Also
* Emacs built-in `project` library: https://github.com/emacs-mirror/emacs/blob/master/lisp/progmodes/project.el
	- https://elpa.gnu.org/packages/project.html
