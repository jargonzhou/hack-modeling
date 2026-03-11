# Emacs Tools

# Installation

```shell
# Windows: https://ftp.gnu.org/gnu/emacs/windows/
# info directory: `D:\software\Emacs\emacs-29.4\share\info`
# HOME: `~\AppData\Roaming`
```

```shell
# Windows WSL2
# X toolkit
➜  emacs-30.2 sudo apt install x11-apps
➜  emacs-30.2 xclock
# X Toolkit Development Libraries
➜  emacs-30.2 sudo apt-get install libxaw7-dev
# font
➜  emacs-30.2 sudo apt-get install libxft-dev
# JetBrains Mono: https://www.jetbrains.com/zh-cn/lp/mono/
# /usr/share/fonts/truetype/jetbrains
# fc-cache -f -v

➜  emacs-30.2 ./configure
➜  emacs-30.2 make
➜  emacs-30.2 sudo make install
➜  emacs-30.2 which emacs
/usr/local/bin/emacs
➜  emacs-30.2 emacs --version
GNU Emacs 30.2
Copyright (C) 2025 Free Software Foundation, Inc.
GNU Emacs comes with ABSOLUTELY NO WARRANTY.
You may redistribute copies of GNU Emacs
under the terms of the GNU General Public License.
For more information about these matters, see the file named COPYING.
```

# Starter Kit
* [Steve Purcell](https://github.com/purcell/emacs.d)
* [Bozhidar Batzov](https://github.com/bbatsov/prelude)

# Mode
* [Dired](./tools/Dired.md): a inbuilt File Manager for Emacs.
* [ElDoc](./tools/ElDoc.md): eldoc-mode is a minor mode which shows you, in the echo area, the argument list of the function call you are currently writing.
* [markdown-mode](https://github.com/jrblevin/markdown-mode): Emacs Markdown Mode. - `M-x package-install RET markdown-mode RET`
* [Org Mode](./tools/Org%20Mode.md): A GNU Emacs major mode for keeping notes, authoring documents, computational notebooks, literate programming, maintaining to-do lists, planning projects, and more — in a fast and effective plain text system.
* [ParEdit](./tools/ParEdit.md): a minor mode for performing structured editing of S-expression data.

# Package Archive, Manager
* [Borg](https://github.com/emacscollective/borg): Assimilate Emacs packages as Git submodules.
* [El-get](https://github.com/dimitri/el-get): Manage the external elisp bits and pieces upon which you depend!
* [GNU ELPA](https://elpa.gnu.org/): GNU Emacs Lisp Package Archive. `M-x list-packages`
* [MELPA](https://melpa.org/): Milkypostman’s Emacs Lisp Package Archive.
* [package.el](https://wikemacs.org/wiki/Package.el): the built-in package manager for GNU Emacs. It was first bundled with Emacs version 24.
* [straight.el](https://github.com/radian-software/straight.el): Next-generation, purely functional package manager for the Emacs hacker.

# Package

```
M-x package-refresh-contents

M-x install-package RET
<package-name> RET

M-x package-list-packages RET
```

```lisp
(require 'package)
;;(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/") t)
;; Comment/uncomment this line to enable MELPA Stable if desired.  See `package-archive-priorities`
;; and `package-pinned-packages`. Most users will not need or want to do this.
(add-to-list 'package-archives '("melpa-stable" . "https://stable.melpa.org/packages/") t)
(package-initialize)
```

Note that you'll need to run `M-x package-refresh-contents` or `M-x package-list-packages` to ensure that Emacs has fetched the MELPA package list before you can install packages with `M-x package-install` or similar.

built-in packages: `M-x package-list-packages` Package > Filter Packages > Filter by Status > 'built-in'
- [package.built-in.txt](./playground.emacs/package.built-in.txt)

* [all-the-icons.el](https://github.com/domtronn/all-the-icons.el): A utility package to collect various Icon Fonts and propertize them within Emacs. Need manually install on Windows.
* [company-mode](https://github.com/company-mode/company-mode): Company is a text and code completion framework for Emacs. The name stands for "**comp**lete **any**thing". It uses pluggable back-ends and front-ends to retrieve and display completion candidates.
* [consult.el](https://github.com/minad/consult): Search and navigate via completing-read
* [corfu.el](https://github.com/minad/corfu): COmpletion in Region FUnction
* [Hydra](https://github.com/abo-abo/hydra): a package for GNU Emacs that can be used to tie related commands into a family of short bindings with a common prefix - a Hydra/九头蛇.
* [multiple-cursors.el](https://github.com/magnars/multiple-cursors.el): place multiple points on screen and edit all of them at the same time.
* [nov.el](https://depp.brause.cc/nov.el/): an EPUB reader for Emacs.

# IDE
* [auto-complete](./tools/auto-complete.md): an intelligent auto-completion extension for Emacs.
* [CEDET](./tools/CEDET.md): a **C**ollection of **E**macs **D**evelopment **E**nvironment **T**ools written with the end goal of creating an advanced development environment in Emacs.
* [Doom Emacs](./tools/Doom%20Emacs.md): a configuration framework for GNU Emacs. - Vim
* [dumb-jump](https://github.com/jacktasia/dumb-jump): an Emacs "jump to definition" package for 60+ languages.
* [EDE](./tools/EDE.md): EDE is the Emacs Development Environment: an Emacs extension that simplifies building and debugging programs in Emacs.
* [Eglot](https://github.com/joaotavora/eglot): A client for Language Server Protocol servers.
* [evil](./tools/evil.md): an **e**xtensible **vi** **l**ayer for Emacs.
* [Flycheck](https://www.flycheck.org/): a modern on-the-fly syntax checking extension for GNU Emacs, intended as replacement for the older Flymake extension which is part of GNU Emacs.
* [format-all](./tools/format-all.md): Auto-format source code in many languages with one command.
* [Helm](./tools/Helm.md): an Emacs framework for incremental completions and narrowing selections.
* [Lisp Mode](https://github.com/emacs-lsp/lsp-mode): Emacs client/library for the Language Server Protocol.
* [Magit](./tools/Magit.md): a complete text-based user interface to Git.
* [Projectile](./tools/Projectile.md): a project interaction library for Emacs.
* [Spacemacs](https://spacemacs.org/): A community-driven Emacs distribution. The best editor is neither Emacs nor Vim, it's Emacs and Vim!
* [Treemacs](./tools/Treemacs.md): a file and project explorer similar to NeoTree or vim’s NerdTree, but largely inspired by the Project Explorer in Eclipse.
* [Yasnippet](./tools/Yasnippet.md): a template system for Emacs.

## Xref

tools to generate an index/tags file of symbols(functions, classes, variabels, ...) in source code
* etags: Emacs `TAGS`
  * https://www.gnu.org/software/emacs/manual/html_node/emacs/Create-Tags-Table.html
  * https://en.wikipedia.org/wiki/Ctags#etags
* ctags: Vi/Vim `tags`
  * https://github.com/universal-ctags/ctags
```shell
rm -rf ctags
find . -type f -iname "*.lisp" | xargs etags -a
```
* gtags: GNU Global, `GTAGS`
  * https://www.gnu.org/software/global/


# Themes
* [Colour schemes for a variety of editors created by Dayle Rees.](https://github.com/daylerees/colour-schemes)
* [Emacs Themes](https://emacsthemes.com/)

```
M-x install-package RET
# last update: 7 years ago: https://github.com/emacsfodder/emacs-slime-theme
slime-theme RET

M-x load-theme RET
slime RET
```

## Zenburn
* https://github.com/bbatsov/zenburn-emacs

> Zenburn for Emacs is a direct port of the popular [Zenburn](http://kippura.org/zenburnpage/) theme for vim, developed by [Jani Nurminen](https://github.com/jnurmine). It's my personal belief (and that of its many users I presume) that it's one of the best low contrast color themes out there and that it is exceptionally easy on the eyes.

```emacs
M-x package-install RET zenburn-theme RET
```

## Solarized
* https://github.com/bbatsov/solarized-emacs
* https://ethanschoonover.com/solarized/

> Solarized is a sixteen color palette (eight monotones, eight accent colors) designed for use with terminal and gui applications. It has several [unique properties](https://ethanschoonover.com/solarized/#features). I designed this colorscheme with both precise [CIELAB](http://en.wikipedia.org/wiki/Lab_color_space) lightness relationships and a refined set of hues based on fixed color wheel relationships. It has been tested extensively in real world use on color calibrated displays (as well as uncalibrated/intentionally miscalibrated displays) and in a variety of lighting conditions.

```emacs
M-x package-install solarized-theme
```

# Misc
## EWW
* [How to make eww default browser in Emacs?](https://emacs.stackexchange.com/questions/7328/how-to-make-eww-default-browser-in-emacs)
```lisp
(setq browse-url-browser-function 'eww-browse-url)
```
* [Emacs-focused Web Browsing](https://www.howardism.org/Technical/Emacs/browsing-in-emacs.html)
* [eaf-browser](https://github.com/emacs-eaf/eaf-browser): A modern, customizable and extensible browser in Emacs

## Proxy
```lisp
(setq url-proxy-services
	  '(("https" . "127.0.0.1:54963"))) ; Lantern
```

## pdf-tools
```
M-x package-install RET pdf-tools RET
M-x pdf-tools-install # use MSYS2
```

# See Also
* [Awesome Emacs](https://github.com/emacs-tw/awesome-emacs): A community driven list of useful Emacs packages, libraries and other items.