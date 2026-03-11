# Emacs
* https://www.gnu.org/software/emacs/
* https://github.com/emacs-mirror/emacs

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

tutorial:
* [A Guided Tour of Emacs](https://www.gnu.org/savannah-checkouts/gnu/emacs/tour/index.html)

books:
* [Learning GNU Emacs](./book.Learning%20GNU%20Emacs.md)
* [Mastering Emacs](./book.Mastering%20Emacs.md)

manual:
* [GNU Emacs Manuals Online](./manual.GNU%20Emacs%20Manuals%20Online.md)

tool:
* [Emacs Tools](./emacs.tools.md)

# Terminology

* `<SPC>`: the space bar

Importance Conventions
* major mode/主模式, minor mode/次要模式
* buffer/缓冲区
* window/窗口, frame/框架
	- modeline, echo area, minibuffer
* point/点, mark/标记, region/区域
	- point: caret/cursor 光标
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
* window: 窗口
* frame: 框架
* buffer: 缓冲区
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
* region: 区域
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
* killing: 消除/剪切, 被删除的内容会进入kill ring
* yanking: 粘贴, 将kill ring中的内容取出 `C-y`
* syntactic unit
* delete
* `<backspace>`
* kill ring: 消除环/剪切环, 存储多次剪切内容的缓冲区
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


# FAQ







<!--
TODO: files
- backup files: `filename~`
- auto-save files: `#filename#`
- garbage files: .log, .toc, .dvi, .bak, .orig, .rej - `dired-garbage-files-regexp`

-->



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

* [Master Emacs in One Year](https://github.com/redguardtoo/mastering-emacs-in-one-year-guide)