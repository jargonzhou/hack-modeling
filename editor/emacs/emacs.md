# Emacs
* https://www.gnu.org/software/emacs/
* [Emacs Reference Cards](https://www.gnu.org/software/emacs/refcards/index.html)
* [emacs-manual.md](./emacs-manual.md)
* [emacs-lisp.md](./emacs-lisp.md)
* [./emacs-tools.md](./emacs-tools.md)

Tutorial:
* [A Guided Tour of Emacs](https://www.gnu.org/savannah-checkouts/gnu/emacs/tour/index.html)

books:
* [Mastering Emacs, 2022](./book.Mastering%20Emacs.md)

> GNU Emacs
>
> An extensible, customizable, free/libre text editor — and more.
> At its core is an interpreter for Emacs Lisp, a dialect of the Lisp programming language with extensions to support text editing.
> 
> The features of GNU Emacs include:
>- Content-aware editing modes, including syntax coloring, for many file types.
>- Complete built-in documentation, including a tutorial for new users.
>- Full [Unicode](http://unicode.org/) support for nearly all human scripts.
>- Highly customizable, using Emacs Lisp code or a graphical interface.
>- A wide range of functionality beyond text editing, including a [project planner](https://www.gnu.org/software/emacs/manual/org.html), [mail and news reader](https://www.gnu.org/software/emacs/manual/gnus.html), [debugger interface](http://www.gnu.org/software/emacs/manual/html_node/emacs/Debuggers.html), [calendar](https://www.gnu.org/software/emacs/manual/html_node/emacs/Calendar_002fDiary.html), [IRC client](https://www.gnu.org/savannah-checkouts/gnu/emacs/erc.html), and [more](https://www.gnu.org/savannah-checkouts/gnu/emacs/further-information.html).
>- A packaging system for [downloading and installing](http://elpa.gnu.org/) extensions.

# Terminology

* `<SPC>`: the space bar

Importance Conventions
* major mode, minor mode
* buffer
* window, frame
	- modeline, echo area, minibuffer
* point, mark, region
	- current buffer
* killing, yanking, copying
	- kill ring
* init file
* XDG: X Desktop Group
* major mode, minor mode
* font locking: syntax highlighting in Emacs

Keys
* comic strip xkcd: https://xkcd.com/378/
* Escape Meta Alt Control Shift
* modifier keys
* key sequence, complete key, prefix key, key maps
* command
* function
	- interactive functions
* minibuffer
* elisp
* `M-S-x`: `M-X` with `X` capitalized
* universal arguments, prefix arguments
* the tempo of typing

configuring Emacs:
* the Customize interface
* faces, options
* evaluating elisp code
* package manager
* color themes

Getting Help:
* symbol
* the Info manual
	- `info`
* Apropos
	- `apropos`
* the Describe system
	- an internal introspection layer

The Theory of Movement 
* local, regional, global
* syntactic unit
* window
* frame
* buffer
* major mode load order
* coding systems
* modeline
* line endings
* scratch buffer
* undo ring
* tab bar
* tab line
* sytax table
* paragraph
* sentence
* defun
* page
* bookmark
* register
* selection
* region
* mark ring
* search
* index
* Isearch
* thing at point
* Occur mode
* Imenu
* Helm
* IDO
* Grep


The Theory of Editing
* character
* word
* line
* sentence
* s-expression
* killing
* yanking
* syntactic unit
* delete
* `<backspace>`
* kill ring
* digit arguments
* negative argument

* fill
* comment
* search
* replace
* regular expression
	- capturing groups
	- meta characters: `\`
* query command
* case folding

# Usage

## Installation
MacOS:
* https://www.emacswiki.org/emacs/EmacsForMacOS
```shell
brew install emacs
ln -Fs $(find /usr/local -name "Emacs.app") /Applications/Emacs.app
```
* or [Emacs For Mac OS X](https://emacsformacosx.com/), 
```shell
➜  bin pwd
/Applications/Emacs.app/Contents/MacOS/bin
➜  bin ls
ctags       ebrowse     emacsclient etags

# create a symbol link for Emacs install with 
➜  MacOS pwd
/Applications/Emacs.app/Contents/MacOS
➜  MacOS cd bin
➜  bin ls
ctags       ebrowse     emacsclient etags
➜  bin ln -s /Applications/Emacs.app/Contents/MacOS/Emacs emacs
➜  bin ls
ctags       ebrowse     emacs       emacsclient etags

export PATH="/Applications/Emacs.app/Contents/MacOS/bin:$PATH"
```
Windows
* https://ftp.gnu.org/gnu/emacs/windows/
	- info directory: `D:\software\Emacs\emacs-29.4\share\info`
	- HOME: `C:\Users\zhouj\AppData\Roaming`
* WSL 
	- https://emacsredux.com/blog/2021/12/19/using-emacs-on-windows-11-with-wsl2/
	- https://github.com/hubisan/emacs-wsl
```shell

The following information may help to resolve the situation:

The following packages have unmet dependencies:
 libgdk-pixbuf-2.0-0 : Breaks: libgdk-pixbuf2.0-0 (< 2.40.0+dfsg-6~) but 2.40.0+dfsg-3ubuntu0.5 is to be installed
 libgdk-pixbuf2.0-0 : Depends: libgdk-pixbuf2.0-common (= 2.40.0+dfsg-3ubuntu0.5) but 2.42.8+dfsg-1 is to be installed
 librsvg2-dev : Depends: gir1.2-rsvg-2.0 (= 2.52.5+dfsg-3) but it is not going to be installed
 mailutils : Depends: guile-2.2-libs but it is not going to be installed
             Depends: libmailutils6 but it is not going to be installed
 texinfo : Depends: libxml-libxml-perl but it is not going to be installed
E: Error, pkgProblemResolver::Resolve generated breaks, this may be caused by held packages.
➜  emacs sudo apt-get install libtree-sitter-dev
Reading package lists... Done
Building dependency tree
Reading state information... Done
E: Unable to locate package libtree-sitter-dev
```

## Install Package

```
M-x install-package RET
<package-name> RET

M-x package-list-packages RET
```

###.1 MELPA
* [ELPA(Emacs Lisp Package Archive)](https://www.emacswiki.org/emacs/ELPA)
* [MELPA(Milkypostman’s Emacs Lisp Package Archive)](https://melpa.org/#/)
	- [Code](https://github.com/melpa/melpa)

## Themes
* 主题库: [Colour schemes for a variety of editors created by Dayle Rees.](https://github.com/daylerees/colour-schemes)
* 展示: [Emacs Themes](https://emacsthemes.com/)
```
M-x install-package RET
# last update: 7 years ago: https://github.com/emacsfodder/emacs-slime-theme
slime-theme RET

M-x load-theme RET
slime RET
```
###.1 Zenburn
* https://github.com/bbatsov/zenburn-emacs
> Zenburn for Emacs is a direct port of the popular [Zenburn](http://kippura.org/zenburnpage/) theme for vim, developed by [Jani Nurminen](https://github.com/jnurmine). It's my personal belief (and that of its many users I presume) that it's one of the best low contrast color themes out there and that it is exceptionally easy on the eyes.

```emacs
M-x package-install RET zenburn-theme RET
```
###.2 Solarized
* https://github.com/bbatsov/solarized-emacs
* https://ethanschoonover.com/solarized/
> Solarized is a sixteen color palette (eight monotones, eight accent colors) designed for use with terminal and gui applications. It has several [unique properties](https://ethanschoonover.com/solarized/#features). I designed this colorscheme with both precise [CIELAB](http://en.wikipedia.org/wiki/Lab_color_space) lightness relationships and a refined set of hues based on fixed color wheel relationships. It has been tested extensively in real world use on color calibrated displays (as well as uncalibrated/intentionally miscalibrated displays) and in a variety of lighting conditions.

```emacs
M-x package-install solarized-theme
```

## auto-complete
* [Code](https://github.com/auto-complete/auto-complete) - last commit 2024-07-21.
* [Doc](https://auto-complete.github.io/)
```
M-x package-install [RET]
auto-complete [RET]
```

> [!info] What is Auto-Complete?
> Auto-Complete is an intelligent auto-completion extension for Emacs. It extends the standard Emacs completion interface and provides an environment that allows users to concentrate more on their own work.

## format-all for Emcas
* [Code](https://github.com/lassik/emacs-format-all-the-code) - last release: 2024-02-06.
* [Formatting Code in Emacs with Format-All](https://ianyepan.github.io/posts/format-all/): a introduction, 2021-06-07.

> [!info] What does it do
? Lets you auto-format source code in many languages using the same command for all languages, instead of learning a different Emacs package and formatting command for each language.
>
> Just do **M-x** `format-all-region-or-buffer` and it will try its best to do the right thing. To auto-format code on save, use the minor mode `format-all-mode`. Please see the documentation for that function for instructions.

* [Auto-formatting a source file in emacs](https://stackoverflow.com/questions/992685/auto-formatting-a-source-file-in-emacs): stackoverflow
	- `M-x mark-whole-buffer`
	- `M-x indent-region`

## ParEdit
* [ParEdit](https://www.emacswiki.org/emacs/ParEdit): ParEdit (`paredit.el`) is a minor mode for performing structured editing of S-expression data.
```
M-x package-install RET paredit RET
```

use with Emacs's Lips modes:
```lisp
; ~/.emacs
    (autoload 'enable-paredit-mode "paredit" "Turn on pseudo-structural editing of Lisp code." t)
    (add-hook 'emacs-lisp-mode-hook       #'enable-paredit-mode)
    (add-hook 'eval-expression-minibuffer-setup-hook #'enable-paredit-mode)
    (add-hook 'ielm-mode-hook             #'enable-paredit-mode)
    (add-hook 'lisp-mode-hook             #'enable-paredit-mode)
    (add-hook 'lisp-interaction-mode-hook #'enable-paredit-mode)
    (add-hook 'scheme-mode-hook           #'enable-paredit-mode)
```

## ElDoc
* [ElDoc](https://www.emacswiki.org/emacs/ElDoc)
> [!info] ElDoc
> A very simple but effective thing, eldoc-mode is a [MinorMode](https://www.emacswiki.org/emacs/MinorMode) which shows you, in the echo area, the argument list of the function call you are currently writing. Very handy. By [NoahFriedman](https://www.emacswiki.org/emacs/NoahFriedman). Part of Emacs.

```lisp
; ~/.emacs
     (add-hook 'emacs-lisp-mode-hook 'eldoc-mode)
     (add-hook 'lisp-interaction-mode-hook 'eldoc-mode)
     (add-hook 'ielm-mode-hook 'eldoc-mode)
```

## Yasnippet
* [Yasnippet](https://www.emacswiki.org/emacs/Yasnippet): EmacsWiki
* [Doc](https://joaotavora.github.io/yasnippet/)
	- **README**: Contains an introduction, installation instructions and other important notes.
	- **Organizing Snippets**: Describes ways to organize your snippets in the hard disk.
		- `yas-snippet-dirs` variable
		- `.yas-partents` file
		- `.yas-setup.el` file
		- `.yas-compiled-snippet.el` file
		- `.yas-skip.el` file
	- **Expanding Snippets**: Describes how YASnippet chooses snippets for expansion at point. Maybe, you'll want some snippets to be expanded in a particular mode, or only under certain conditions, or be prompted using ido, etc…
		- `yas-minor-mode`
		- `TAB`: `yas-expand`
		- `M-x yas-insert-snippet`: `C-C & C-s`
	- **Writing Snippets**: Describes the YASnippet definition syntax, which is very close (but not equivalent) to Textmate's. Includes a section about converting TextMate snippets.
		- `M-x yas-new-snippet`: `C-c & C-n`
	- **The YASnippet menu**: Explains how to use the YASnippet menu to explore, learn and modify snippets.
	- **Frequently asked questions**: Answers to frequently asked questions.
	- **YASnippet Symbol Reference**: An automatically generated listing of all YASnippet commands, (customization) variables, and functions.
* [Code](https://github.com/joaotavora/yasnippet)
	- [Yasnippet official snippet collections](https://github.com/AndreaCrotti/yasnippet-snippets): `M-x package-install RET yasnippet-snippets RET`
> [!info] Yasnippet
> **YASnippet** is a template system for Emacs. It allows you to type an abbreviation and automatically expand it into function templates. Bundled language templates include: C, C++, C#, Perl, Python, Ruby, SQL, LaTeX, HTML, CSS and more. The snippet syntax is inspired from [TextMate's](http://manual.macromates.com/en/snippets) syntax, you can even [import](https://github.com/joaotavora/yasnippet#import) most TextMate templates to YASnippet. Watch [a demo on YouTube](http://www.youtube.com/watch?v=ZCGmZK4V7Sg).
```
M-x package-install RET yasnippet RET
```
``` lisp
(require 'yasnippet)
(yas-global-mode 1)
```
* [YASnippet menu](https://joaotavora.github.io/yasnippet/snippet-menu.html)
* [Writing snippets](https://joaotavora.github.io/yasnippet/snippet-development.html)

## Atom Slime
* [SLIMA](https://github.com/neil-lindquist/slima): now ~~Atom~~Pulsar

## markdown-mode

```
M-x package-install RET markdown-mode RET
```

## Dired
* [wiki](https://wikemacs.org/wiki/Dired)
> [!info] Dired
> Dired is a inbuilt File Manager for Emacs. Its arguably the best file manager with the functionality it possesses. Unlike any other file managers the directory listing is just as an another buffer of Emacs with dired-mode as Major Mode.
* [[Dired Reference Card.v29.pdf]]

###.1 Dirvish
* [Code](https://github.com/alexluigit/dirvish)
> [!info] Dirvish
> Dirvish is an improved version of the Emacs inbuilt package [Dired](https://www.gnu.org/software/emacs/manual/html_node/emacs/Dired.html). It not only gives Dired an appealing and highly customizable user interface, but also comes together with almost all possible parts required for full usability as a modern file manager.

## EDE
* [Doc](https://www.gnu.org/software/emacs/manual/html_mono/ede.html)
> [!info] EDE
> EDE is the Emacs Development Environment: an Emacs extension that simplifies building and debugging programs in Emacs. It attempts to emulate a typical IDE (Integrated Development Environment). EDE can manage or create your makefiles and other building environment duties, allowing you to concentrate on writing code rather than support files. It aims to make it much easier for new programmers to learn and adopt GNU ways of doing things.

* [CEDET](https://cedet.sourceforge.net/): CEDET is a **C**ollection of **E**macs **D**evelopment **E**nvironment **T**ools written with the end goal of creating an advanced development environment in Emacs. - Last Update: 2019-07-09
	- [A Gentle introduction to CEDET](https://alexott.net/en/writings/emacs-devenv/EmacsCedet.html) - 2014.


## all-the-icons.el
* [Code](https://github.com/domtronn/all-the-icons.el): A utility package to collect various Icon Fonts and propertize them within Emacs.
Need manually install on Windows.

## evil
* https://github.com/emacs-evil/evil

> [!info] Evil
> Evil is an **e**xtensible **vi** **l**ayer for [Emacs](http://www.gnu.org/software/emacs/). It emulates the main features of [Vim](http://www.vim.org/), and provides facilities for writing custom extensions. Also see our page on [EmacsWiki](http://emacswiki.org/emacs/Evil).

## Projectile
* [Code](https://github.com/bbatsov/projectile)
	- [extensions](https://melpa.org/#/?q=projectile)
* [Doc](https://docs.projectile.mx/projectile/index.html) 
* Emacs built-in `project` library: https://github.com/emacs-mirror/emacs/blob/master/lisp/progmodes/project.el
	- https://elpa.gnu.org/packages/project.html
> [!info] Projectile
**Projectile** is a project interaction library for Emacs. Its goal is to provide a nice set of features operating on a project level without introducing external dependencies (when feasible). For instance - finding project files has a portable implementation written in pure Emacs Lisp without the use of GNU `find` (but for performance sake an indexing mechanism backed by external commands exists as well).
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

## EWW
* [How to make eww default browser in Emacs?](https://emacs.stackexchange.com/questions/7328/how-to-make-eww-default-browser-in-emacs)
```lisp
(setq browse-url-browser-function 'eww-browse-url)
```
* [Emacs-focused Web Browsing](https://www.howardism.org/Technical/Emacs/browsing-in-emacs.html)
* [eaf-browser](https://github.com/emacs-eaf/eaf-browser): A modern, customizable and extensible browser in Emacs

## Starter Kit

| Starter Kit               | Link                                   |
| :------------------------ | -------------------------------------- |
| Steve Purcell             | https://github.com/purcell/emacs.d     |
| Bozhidar Batzov           | https://github.com/bbatsov/prelude     |
| Spacemacs - Emacs and Vim | https://spacemacs.org/                 |
| Doom Emacs - Vim          | https://github.com/hlissner/doom-emacs |

## Third-Party Packages and Tools

| Name               | Description                                                                                      | Link                                                                      |
| :----------------- | ------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------- |
| nov                | an EPUB reader for Emacs                                                                         | https://depp.brause.cc/nov.el/                                            |
| Magit              | a Git UI with chord-based key system                                                             | https://www.magit.vc                                                      |
| Multiple Cursors   | place multiple points on screen and edit all of them at the same time                            | https://github.com/magnars/multiple-cursors.el                            |
| LSP mode and EGlot | language server interfaces for Emacs                                                             | https://github.com/emacs-lsp/lsp-mode https://github.com/joaotavora/eglot |
| Helm               | a powerful completion framework                                                                  | https://emacs-helm.github.io/helm/                                        |
| Flycheck           | a generic framework for linting and syntax error checker codes.                                  | https://www.flycheck.org/en/latest/                                       |
| ORG mode           | an exceptional organizer, diary and agenda manager, literate programing tool and mode.           | https://orgmode.org/                                                      |
| YASnippet          | a text snippet expansion tool                                                                    | http://joaotavora.github.io/yasnippet/                                    |
| Hydra              | a package to build flexible popup UIs for key bindings.                                          | https://github.com/abo-abo/hydra                                          |
| dumb-jump          | jump to definitions from symbols under point.                                                    | https://github.com/jacktasia/dumb-jump                                    |
| ripgrep            | a line-oriented search tool that recursively searches the current directory for a regex pattern. | https://github.com/BurntSushi/ripgrep                                     |


# FAQ
* [How to find a file in Emacs without known exact directory?](https://stackoverflow.com/questions/4340949/how-to-find-a-file-in-emacs-without-known-exact-directory)
```
# prompted for root directory to search with a file mask
M-x find-name-dired
```

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

* 设置字体
* [Set Fonts](https://www.emacswiki.org/emacs/SetFonts)
* [stackoverflow: How to set the font size in Emacs?](https://stackoverflow.com/questions/294664/how-to-set-the-font-size-in-emacs)
```
M-x customize-face RET default
```

* 行号
```lisp
;;; global line number
;;; https://www.gnu.org/software/emacs/manual/html_node/efaq/Displaying-the-current-line-or-column.html
;;; https://www.emacswiki.org/emacs/LineNumbers
;;; (setq column-number-mode t)
(global-display-line-numbers-mode 1)
```

* 字符编码
* [Emac Language Environment](https://www.emacswiki.org/emacs/LanguageEnvironment)

``` lisp
(set-terminal-coding-system "UTF-8")
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


# See Also
* [EmacsWiki](https://www.emacswiki.org/emacs?interface=en): The **[EmacsWiki](https://www.emacswiki.org/emacs/EmacsWiki)** is dedicated to documenting and discussing [EmacsAndXEmacs](https://www.emacswiki.org/emacs/EmacsAndXEmacs) and [EmacsLisp](https://www.emacswiki.org/emacs/EmacsLisp). See the [MissionStatement](https://www.emacswiki.org/emacs/MissionStatement) for more information.
* [EWS(Emacs Writing Studio)](https://lucidmanager.org/tags/emacs/): a minimalist configuration that helps authors to research, write and publish articles books and websites. - *a series of articles on Emacs*.

* Blogs

| Blog                    | Link                                     |
| :---------------------- | :--------------------------------------- |
| Mastring Emacs          | https://www.masteringemacs.org/          |
| Sacha Chua              | https://sachachua.com/blog/              |
| Irreal’s Emacs blog     | https://irreal.org/blog/                 |
| Artur Malabarba         | https://endlessparentheses.com/          |
| Bozhidar Batzov         | https://batsov.com/                      |
| John Kitchin            | https://kitchingroup.cheme.cmu.edu/blog/ |
| Planet Emacs aggregator | https://planet.emacslife.com/            |
