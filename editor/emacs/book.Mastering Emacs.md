# Notes of 'Mastering Emacs'

| #    | Title                            | Progress | Description |
| :--- | :------------------------------- | :------- | :---------- |
| 1    | [[#5.1 Introduction]]            | 100%     | 2024-09-03  |
| 2    | [[#5.2 The Way of Emacs]]        | 100%     | 2024-09-04  |
| 3    | [[#5.3 First Steps]]             | 100%     | 2024-09-08  |
| 4    | [[#5.4 The Theory of Movement]]  | 100%     | 2024-10-07  |
| 5    | [[#5.5 The Theory of Editing]]   | xxx%     | yyyy-mm-dd  |
| 6    | [[#5.6 The Practicals of Emacs]] | xxx%     | yyyy-mm-dd  |
| 7    | [[#5.7 Conclusion]]              | 100%     | 2024-10-07  |

# 1 Tips for Recapture

<!-- 帮助重温的过程总结. -->

1. Step 1

# 2 术语

<!-- 记录阅读过程中出现的关键字及其简单的解释. -->

<!-- 进展中需要再次确认的术语:

进行中: 术语1
已完成: ~~术语1~~
-->



# 3 介绍

<!-- 描述书籍阐述观点的来源、拟解决的关键性问题和采用的方法论等. -->

# 4 动机

<!-- 描述阅读书籍的动机, 要达到什么目的等. -->

# 5 概念结构

<!-- 描述书籍的行文结构, 核心主题和子主题的内容结构和关系. -->
## 5.1 Introduction

2022: Emacs 28, native compilation feature.

future:
- Langauge Server
	- js2-mode
	- nxml-mode
	- CEDET
	- tree sitter

What you need to be productive in Emacs: 6 things
- 1. **what Emacs is about**
	- terminology, conventions, philosophy.
- 2. **getting started with Emacs**
	- install, run, the Customize interface, the user interface of Emacs.
- 3. **discovering Emacs**
	- the self-documenting nature.
- 4. **movement**
	- move by syntactic units
	- use windows and buffers
	- search and index text
	- select text
	- use the mark.
- 5. **editing**
	- edit text by balanced expressions, words, lines, paragraphs
	- create keyboard macros to automate repetitive tasks
	- search and replace
	- registers
	- multi-file edit
	- abbreviations
	- remote file edit
- 6. **productivity**
	- integration with hundreds of external tools.

## 5.2 The Way of Emacs
GNU Emacs

### 5.2.1 Guiding Philosophy
Emacs is a tinkerer's editor. Plain and simple. (tinkerer: 喜欢捣鼓小器具、小发明的人.)
- an original extensible, customizable, self-documenting editor.

Emacs pulls you in:
- use Emacs for IRC, email, database access, organize your thoughts, command-line shells, compile code, surf the internet: just as easy as editing text.
- keep key bindings, theme, and all the power of Emacs and elisp to configure or alter the behavior of everything.
- avoid the context switches of going from application to application.

If you want to modify Emacs, or any of the myriad packages available to you, **Emacs Lisp(elisp)** is what you will have to write.

If want everything to work perfectly out of the box, not want to tweak anything:
- use a starter kit
- use the defaults

| Starter Kit               | Link                                   |
| :------------------------ | -------------------------------------- |
| Steve Purcell             | https://github.com/purcell/emacs.d     |
| Bozhidar Batzov           | https://github.com/bbatsov/prelude     |
| Spacemacs - Emacs and Vim | https://spacemacs.org/                 |
| Doom Emacs - Vim          | https://github.com/hlissner/doom-emacs |

> [!info] LISP?

Emacs is powered by its own LISP implementation called Emacs Lisp(elisp).
The data-as-code, the macro system and the ability to advise arbitrary function, give you an unprecedented ability to alter Emacs to suit your needs:
- modify the behavior of existing code without copying and modifying the original.
- you can hook, replace or alter existing routines in Emacs to suit your needs without rewriting large swatches of someone else's source code.

**Emacs as an Operating System**
Emacs is like a magpie's nest of shiny things: (magpie: 喜鹊, 有收集零碎东西癖好的人)
- `M-x zone`: a built-in screensaver.
- `M-x dunnet`: a text adventure game.
- `M-x tetris`: Tetris game. 俄罗斯方块.
- client-server model.
- a lunar phases calculator.
- `M-x doctor`: a psychotherapist.
- several email clients.
- an artist mode: draw ASCII art.
- `EXWM`: an Emacs-based X window manager.
- EPUB reader: `nov`
When you run Emacs, you are in fact launching **a tiny C core** responsible for the low-level interactions with your operating system's ABI.
The cornerstone of Emacs though it the elisp **interpreter**: with release of Emacs 28, all elisp code is compiled to native code, result in significant speedups.
When you write elisp, your are **altering a living system**: an operating system running on an operating system.
When you ask Emacs a question, you are asking your Emacs what its **state** is.
Emacs has an excellent elisp **debugger** and unlimited access to every facets of Emacs's own interpreter and state.

`Mx emacs-uptime`: an uptime counter

> [!info] Extensibility

- a speech interface for the bind: [emacsspeak](https://emacspeak.sourceforge.net/)
- remote file editing: TRAMP(Transparent Remote (file) Access, Multiple Protocol) including SSH, FTP, Docker, rclone, rsync and more.
- Shell access: a built-in ANSI-capable Terminal emulator, an Emacs wrapper around shells(bash etc), Eshell written in elisp.
- ORG mode: a to-do, agenda, project planner, literate programming, note-taking application.
- symbolic calculator: Reverse-Polish Notation calculator
- music player: EMMS(Emacs Multimedia System)
- much more: 
	- support for almost every programming environment
	- built-in man page and info reader
	- a directory and file manager
	- support for almost every major version control system
	- thousands of other features.

### 5.2.2 Important Conventions

> [!info] The Buffer

In Emacs, all files are buffers, but not all buffers are files.
example:
- files, edit text
- I/O device, talk to another process: bash, Python

In Emacs, the buffer is the **data structure**:
- almost all Emacs's own command act on buffers.
- the very same commands used to move around and edit in Emacs are almost always the same ones used behind-the scenes in elisp.

> [!info] The Window and the Frame

A buffer is displayed in a **window** on the screen.
In Emacs, a window is a tiled portion(平铺的部分) of the **frame**, which is what most window managers call a window.
- each frame can have one or more windows: for the window to be visible to the user, it must be in a frame.
- each window can have exactly one buffer: a buffer must be viewed in a window to be displayed to the user.

**Modeline**, **Echo Area** and **Minibuffer**
- buffer content
```lisp
(defun insert-hello-world ()
  (interactive)
  (insert "Hello, World!"))
```
- **Modeline**: Emacs use it to communicate facts about Emacs and the buffer you're in.
	- `*scratch*`: buffer name
	- `Lisp Interaction`: major mode
```
-UUU:**--F3 *scratch* All L4 (Lisp Interaction) --
```
- **Minibuffer**: directly below the modeline
	- it's where errors and general information are shown. 
	- it's nearly identical to a normal buffer: edit command.
	- it's how you communicate with Emacs: write the string you want to search for in the minibuffer.
	- `M-x`: Emacs's extended command functionality
	- `insert-hello-world`: the command
```
-UUU:**--F3 *scratch* All L4 (Lisp Interaction) --
M-x insert-hello-world
```
- **Echo Area**: share the same spot on the screen with minibuffer.

> [!info] The Point and Mark

**Point**: caret, cursor
- the current position in a buffer.
- each buffer tracks the position of the point separately.
- notation in book: `█`
**Region**:
- the point and mark represent the boundary for a region.
- a contiguous block of text, usually in the current buffer.
- in other editors: the selection or the highlight.
- TMM(Transient Mark Mode): support visual regions.
**Mark**:
- serves as a boundary for the region.
- a beacon(灯塔, 界标) you can use to return to from other parts in the buffer.

> [!info] Killing, Yanking and CUA

Cut, copy, paste most a `Ctrl+x`, `Ctrl+c`, `Ctrl+v`.
In Emacs:
- Killing: cut
- Yanking: paste
- Copying: save to the kill ring.

most of the keys and terminology stem from
- CUA: IBM's Common User Access, introduced in 1987
- Apple.

> [!info] `.emacs.d`, `init.el`, `.emacs`

init file:
- `~/.emacs`
- `~/.emacs.d/init.el`: Linux
- `%HOME%\init.el`: Windows - FIX: Use 'Open Home Directory' link, example `c:/Users/zhouj/AppData/Roaming`.
- `~/.config/emacs/init.el`: [[#9.2 XDG(X Desktop Group)|XDG]] convention of user configuration on Linux

`C-h v` `user-emacs-directory RET`: show init file folder.

> [!info] Major Modes and Minor Modes

**Major modes** in Emacs control how buffer behaves.
- *example*: the Python major mode
- each buffer will always have a major mode.
- can introduce: 
	- **font locking**(syntax highlighting): made up of **faces** of properties(color, font, text size, etc), 
	- advanced indentation engine,
	- specialized commands.
- file with extension: *a centralized register* that map file extensions to major modes.
- file without extension: *scan the first portion of the file* and try to infer the major mode.
- always displayed in the modeline.
**Minor modes**:
- optional add-ons that enable for some or all of buffers.
- *example*: flyspell mode, a minor mode that spell checks text as you write.
- some are diaplayed in the modeline.

## 5.3 First Steps

### 5.3.1 Installing and Starting Emacs

```shell
emacs --version

apt-get install emacs28
# build from source: build and install Emacs's dependencies
# then configure, make, make install
apt-get build-dep emacs28
```

> [!info] Starting Emacs
- GUI Emacs
- Terminal Emacs
```shell
emacs
# run in terminal
emacs -nw

# prevent load init file
emacs -q
```

Emacs Client-Server
activate client-server mode:
- `M-x server-start`: launch a server inside an already running Emacs instance, the instance turns into a server.
- `emacs --daemon`: run Emacs as a daemon, it will call `server-start`.
- systemd: `systemctl --user enable emacs`
- go the server route: `emacsclient`, set `$EDITOR` environment variable to `emacsclient`
advantages:
- a persistent session
- work well with `$EDITOR`
- fast file opening: from command line use the `emacsclient` binary.
```
M-x server-mode
M-x server-force-delete
```

### 5.3.2 The Emacs Interface

the splash screen.
in Terminal Emacs, access the menu bar use `F10`.

### 5.3.3 Keys

Emacs is famous for two things: 
- its obscure keyboard incantations and that - 晦涩的键盘咒语.
- it’s the kitchen sink editor that can do everything - 可以做任何事情的厨房洗涤槽. kitchen sink: 无所不包, 一应俱全.
- [xkcd 378: Real Programmers](https://xkcd.com/378/)

**modifier keys**: 修改键

| Modifier | Full Name                             |
| :------- | :------------------------------------ |
| `C-`     | Control                               |
| `M-`     | Meta, Alt                             |
| `S-`     | Shift                                 |
| `s-`     | Super, for historical reasons         |
| `H-`     | Hyper, for historical reasons         |
| `A-`     | Alt, for historical reasons, not used |

**key sequence**: a sequence of keyboard or mouse actions.
**complete key**: one or more keyboard sequences that invoke a command.
**prefix key**: the sequence of keys is not a complete key.
- basically subdivision: a way of grouping keys and increasing the number of possible key combinations.
- **key maps**: sets of keys that belong to a particular prefix key.
- example: `C-x`.

examples:

| Key Binding            | Description                                              |
| :--------------------- | :------------------------------------------------------- |
| `C-d`                  | command `delete-char`                                    |
| `C-M-d`                | similar to `C-d`                                         |
| `C-x`                  | prefix key                                               |
| `C-x C-f`              | command `find-file`                                      |
| `C-x 8 P`              | insert the paragraph symbol ¶. 2 prefix keys: `C-x`, `8` |
| `C-M-%`                | command `M-x query-replace-regexp`                       |
| `TAB`, `F1`-`F12`, ... | `<tab>`, `<f1>`, ...                                     |
| `C-g`                  | bail me out                                              |

> [!info]  Caps Lock as Control

rebind your caps lock key to control.
- Windows: [SharpKeys](https://github.com/randyrants/sharpkeys)
- Ubuntu, MacOS: Keyboard setting.
- Other Linux distribution: `xmodmap`.

> [!info]  `M-x`: Execute Extended Command

pronounced: mex, M x, meta x.
In minibuffer, a prompt will appear and wen can input the name of a command we wish to run.
example: `M-x lunar-phases RET`

auto completion: `TAB`
`M-x` is written in elisp and bound to a key just like everything else.

> [!note] Commands and Functions 
> Command: a type of function that is accessible to the user.
> For a function to be accessible to a user, it must be **interactive**(an Emacs term for a function that has additional properties associated with it, rendering it usable through the execute extended command `M-x` interfae and key bindings).

> [!info]  `M-S-x`: Execute Extended Command for Buffer

added in Emacs 28: *restrict executable command to a curated selection relevant to the current buffer*.
another way of writing: `M-X`, with the `X` capitalized.

> [!info]  Universal Arguments

access commands' alternate *states*: **universal argument**, **prefix argument**.
- Emacs's command states are merely **numbers**.
key binding: `C-u`. 
When you *prefix* another key binding, you are telling Emacs to modify the functionality of that command.
If a command has N states, we can type `C-u` up to N times.
The universal argument is shorthand for the number **4**.
Universal argument on their own are totally *inactive*: Emacs wait until we give it a following command.

| Key Binding | Description             |
| :---------- | :---------------------- |
| `C-u a`     | print `aaaa` on screen. |
| `C-u C-u a` | print 16 characters.    |
| `C-u 10 a`  | print 10 characters.    |
command: `self-insert-command`, when invoked, insert the last typed key.

pass **digit arguments** to a command: 

| Key Binding        | Description       |
| :----------------- | :---------------- |
| `C-u`              | 4                 |
| `C-u C-u`          | 16                |
| `C-u C-u ...`      | 4^n               |
| `M-0` to `M-9`     | 0-9               |
| `C-0` to `C-9`     | 0-9               |
| `C-M-0` to `C-M-9` | 0-9               |
| `C--`              | negative argument |
| `M--`              | negative argument |
| `C-M--`            | negative argument |

example: **tempo of typing** 打字节奏

| Key Binding | Description                                                    |
| :---------- | :------------------------------------------------------------- |
| `M-- M-d`   | kill the previous word before point. - *maintains* your tempo. |
| `C-- M-d`   | same as `M-- M-d`. - *breaks* your tempo.                      |

> [!info]  Discovering and Remembering Keys

append `C-h` to any prefix to get a list of all bindings that belongs to that key map.
example:

| Key Binding | Description                                   |
| :---------- | :-------------------------------------------- |
| `C-x 8 C-h` | display keys and commands of `C-x 8` key map. |

### 5.3.4 Configuring Emacs

choices to change Emacs:
- use the Customize interface.
- write elisp.

> [!info]  The Customize Interface

The customize interface is divided into **groups** and **sub groups**.
- each group represents one package, mode, or piece of functionality.
- top-level group is call `Emacs`.
- buffer: `*Customize Group: Emacs*`.
- search bar: search for customizable options.
- make up of **faces** and **options**.
	- options are a catch-all term for things you can customize that aren't faces.
	- example: face `font-lock-string-face`
- `Apply and Save`: persistent changes.
- `Revert...`:
	- `Revert This Session's Customizations`
	- `Erase Customizations`
- all customizations are stored in init file by default.

commands:

| Command                    | Description                                                   |
| :------------------------- | :------------------------------------------------------------ |
| `M-x customize`            | display the Customize interface and all the groups.           |
| `M-x customize-option`     | open the Customize UI with option entered.                    |
| `M-x customize-browse`     | open a tree group browser.                                    |
| `M-x customize-customized` | customize options and faces that have changed but not saved.  |
| `M-x customize-changed`    | display all options changed since a particular Emacs version. |
| `M-x customize-face`       | prompt for the name of a face to Customize.                   |
| `M-x customize-group`      | prompt for a group name to Customize.                         |
| `M-x customize-mode`       | customize the major mode of current buffer.                   |
| `M-x customize-saved`      | display all saved options and faces.                          |
| `M-x customize-themes`     | show a list of installed themes.                              |
> [!info]  Evaluating Elisp Code

| Command           | Description                           |
| :---------------- | :------------------------------------ |
| `M-x eval-buffer` | evaluate the entire buffer.           |
| `M-x eval-region` | evaluate just the region have marked. |
> [!info]  The Package Manager

Emacs comes with a **package manager** that displays and installs packages from centralized **repositories**.
- GNU ELPA
- NonGNU ELPA
- [[index.Emacs#6.3.1 MELPA|MELPA]]

| Command                        | Description                                                |
| :----------------------------- | :--------------------------------------------------------- |
| `M-x package-list-packages`    | retrieve the package listing from configured repositories. |
| `M-x package-install`          | install packages.                                          |
| `M-x package-refresh-contents` | refresh the repository catalog.                            |
> [!info]  Custom Color Themes

| Command                   | Description                   |
| :------------------------ | :---------------------------- |
| `M-x customize-themes`    | list installed custom themes. |
| `M-x list-colors-display` | list supported color names    |
### 5.3.5 Getting Help
Emacs is a self-documenting editor: every facet of Emacs is searchable or describable.
**symbol**: express anything can look up, including variable, function, face, etc.

> [!info]  The Info Manual

Emacs's own manual are written in [[#9.2 GNU Texinfo|TeXinfo]].
- command line tool `info`: TeXinfo hypertext viewer.
- Emacs has its own info viewer/browser.

| Key Binding   | Command            | Description                                        |
| :------------ | :----------------- | :------------------------------------------------- |
| `C-h i`       | `M-x info`         | access Emacs's info reader                         |
|               | `M-x info-apropos` | search all info manual pages for matching pattern. |
| `C-h R`       |                    | Emacs 28: open manual.                             |
| `C-h R eintr` |                    | Emacs 28: open 'Emacs Lisp Intro'.                 |
| `C-h F`       |                    | lookup the documentation for a command.            |

keyboard shortcuts for navigation in the `info` documentation browser:

| Key Binding | Description                              |
| :---------- | :--------------------------------------- |
| `[`, `]`    | previous/next node.                      |
| `l`, `r`    | go back/forward in history               |
| `n`, `p`    | previous/next sibling node               |
| `u`         | go up one level to a parent node         |
| `SPC`       | scroll one screen at a time              |
| `TAB`       | cycle through cross-references and links |
| `RET`       | open the active link                     |
| `m`         | prompt for a menu item name and open it  |
| `q`         | close the info browser                   |

Emacs's **bookmark** system:
- info pages, files, directories, etc.

> [!info]  Apropos

Emacs has an **apropos system** that works in much the same way as `apropos` on the command line.
- applicable if you are not entirely sure what you are looking for.
- `M-x apropos-command`, `C-h a`: show all commands that match a given pattern.
	- example: `C-h a` `-word$`, search commands that work on words.
- custom sort results: `M-x customize-option RET apropos-sort-by-scores RET`.
commands:

| Key Binding | Command                     | Description                                                  |
| :---------- | :-------------------------- | :----------------------------------------------------------- |
|             | `M-x apropos`               | display all symbols that match a given pattern.              |
| `C-h a`     | `M-x apropos-command`       | list only the commands.                                      |
| `C-h d`     | `M-x apropos-documentation` | search just the documentation.                               |
|             | `M-x apropos-library`       | list all variables and functions defined in a library.       |
|             | `M-x apropos-user-option`   | show user options available through the Customize interface. |
|             | `M-x apropos-value`         | search all symbols with a particular value.                  |
example: `C-h a` `-word$`, search commands that work on words.

| Key Binding | Command       | Description                                                 |
| :---------- | :------------ | :---------------------------------------------------------- |
| `M-$`       | `ispell-word` | example: check spelling of word under or before the cursor. |
| `M-d`       | `kill-word`   | kill characters forward until the end of a word.            |
| `C-<left>`  | `left-word`   | move point N word to the left.                              |
| `M-@`       | `mark-work`   | set mark `ARG` words away from point.                       |
> [!info]  The Describe System

If you know what you are looking for, then describe will explain what it is.
- Every facets of Emacs is accessible and indexed through the describe system.
	- code written in elisp
	- the core layer written in C
	- keys, commands, character sets, coding systems, fonts, faces, modes, syntax tables and more.
- The describe system is not static.
	- fetch the details through *an internal introspection layer* which itself queries Emacs's own *internal data structures*.

the describe system of commands.

| Key Binding | Command                 | Description                                                                                                           |
| :---------- | :---------------------- | :-------------------------------------------------------------------------------------------------------------------- |
| `C-h m`     | `M-x describe-mode`     | display the documentation for the major mode (and any minor modes) along with the keybindings introduced by the mode. |
| `C-h x`     | `M-x describe-command`  | describe commands not functions.                                                                                      |
| `C-h f`     | `M-x describe function` | describe a function.                                                                                                  |
| `C-h v`     | `M-x describe-varaible` | describe a variable.                                                                                                  |
| `C-h k`     | `M-x describe-key`      | describe what a key binding does.                                                                                     |

Emacs 28 adds shortcuts to all *describe buffers*:

| Key Binding | Description                    |
| :---------- | :----------------------------- |
| `i`         | open the info manual.          |
| `s`         | jump to the source definition. |
| `c`         | open the Customize interface.  |

## 5.4 The Theory of Movement

Movement in Emacs is local, regional or global.
- **local**: when edit and move around text near to the *point*.
- **regional**: similar to local, but involves whole functions or class definitions, chapters and such constructs.
- **global**: anything that takes you from one buffer to another, or from one window to the next.

**syntactic unit**:
- a term for commands that operate on a group of characters.
- is a character, word, line, sentence, paragraph, balanced expression and so forth.

a tiling window manager
In Emacs, windows are transient: they come and go as you need them.
Buffers are rarely killed/close when they are no longer needed.

### 5.4.1 The Basics

| Key Binding           | Description                                                                  |
| :-------------------- | :--------------------------------------------------------------------------- |
| `C-x C-f`             | find/open a file                                                             |
| `C-x C-s`             | save the buffer                                                              |
| `C-x C-w`             | write to a new file                                                          |
| `C-x s`               | save all files.                                                              |
| `C-x b`               | switch buffer                                                                |
| `C-x k`               | kill/close a buffer                                                          |
| `C-x C-b`             | display all open buffers                                                     |
| `C-x C-c`             | exit Emacs                                                                   |
| `ESC ESC ESC`         | exit out of prompts, regions, prefix arguments and return to just one window |
| `C-/`, `C-_`, `C-x u` | undo changes                                                                 |
| `F10`                 | activate the menu bar in Terminal Emacs.                                     |

> [!info] `C-x C-f`: Find file

Emacs does not distinguish between opening an existing file and creating a new file.

> Major mode load order

- 1. file-local variables: safe, unsafe
```
# header
-*- mode: mode-name-here; my-variable: value -*-

# footer
Local Variables:
mode: mode-name-here
my-variable: value
End:
```
- 2. program loader directives, shebangs: `#!`: the variable `interpreter-mode-alist` lists the program loaders Emacs can detect.
```
#!/usr/bin/env python
#!/bin/bash
```
- 3. magic mode detection: use the variable `magic-mode-alist` to see if the beginning of the file matches a pattern in this variable.
- 4. automatic mode detection: use the variable `auto-mode-alist` to match a file extension, file name or all or parts of a file's path.
```
/etc/passwd  # etc-passwd-generic-mode
.zip         # archive-mode
```

**Coding systems**:
- Emacs support Unicode, including transparently read and write between different coding systems, bidirectional right-to-left script support, keyboard input method switching and more.
- `C-h C <RET>`: see the coding system in use for the current buffer.
```
# modeline
U:**- helloworld.c 92% of 5k ...
```
- `U` means the buffer `helloworld.c` has a multi-byte coding system.

**Line endings**:
- `:` after `U` means UNIX-style line ending.
- `(DOS)`: DOS.
- `(Mac)`: Macintoshes.
```
# modeline
U:**- helloworld.c 92% of 5k ...
```

> [!info] `C-x C-s`: Save Buffer

- `C-x C-w`: write to a new file
- `C-x s`: save all files.

> [!info] `C-x C-c`: Exit Emacs

- Emacs will only exit after asking you if you want to save unsaved files.
- `C-_`, `C-x u`, `Edit -> Undo`, undo button.

> [!info] `C-x b`: Switch Buffer

- default action: the name of the last buffer you visit
- **scratch buffers**: buffers that create and use but not intend to permanently save.

> Buffer Switching Alternatives

- built-in `TAB`-completion
- completion frameworks
	- IDO mode: Emacs 27-, `M-x ido-mode`
	- FIDO mode: Emacs 27+, `M-x fido-mode`, under group `icomplete`
	- Helm, ivy, Selectrum, Icicles, Icomplete
```
# enable permanently
M-x customize-option ido-mode
# enable flex matching: fuzzy matching
M-x customize-option ido-enable-flex-matching RET
# more features
M-x custom-group ido

# coustom fido mode
M-x customize-group icomplete
```

> [!info] `C-x C-b`: Display All Open Buffers

- alternative: `M-x ibuffer`
```lisp
(global-set-key [remap list-buffers] 'ibuffer)
```

> [!info] `C-x k`: Kill Buffer

Normally, serious Emacs users have hundreds or even thousands of open buffers at a time.

> [!info] `ESC ESC ESC`: Keyboard Escape

go back to normal:
exit out of prompts, regions, prefix arguments and return to just one window

> [!info] `C-/`: Undo

undo changes

**undo ring**:
- instead of storing changes make in a list that can undo and redo from, in Emacs it's stored in the undo ring.
- every action take is recorded in the undo ring, and this include the act of undoing something.
- Emacs group certain commands together into on cohesive undo *cell*
	- typing character
	- repeating the same command many time in a row
- Some events always seal the undo record and *start a new one* - seal: 密封
	- `RET`
	- backspace
	- moving the point around.
- alternative: [Undo Tree](https://www.emacswiki.org/emacs/UndoTree)
example:
```
Hello
Emacs█

# C-/
Hello
█

# C-/
Hello█

Hello
World█

# C-/ twice
Hello
Emacs█

# alter Hello to GNU
GNU█
Emacs

# repeatly C-/: end up with a blank buffer.
```

simulate the classic undo-redo behavior:
- `M-x undo-redo`: Emacs 28+, `C-?`, `C-M-_`, a redo command for undo.
- `M-x undo-only`: will not redo a previous undo.

### 5.4.2 Window Management

| Key Binding | Description              |
| :---------- | :----------------------- |
| `C-x 0`     | delete the active window |
| `C-x 1`     | delete other windows     |
| `C-x 2`     | split window below       |
| `C-x 3`     | split window right       |
| `C-x o`     | switch active window     |

remember window settings: Winner mode

| Key Binding       | Description          |
| :---------------- | :------------------- |
| `M-x winner-mode` | enable winner mode   |
| `C-c <left>`      | undo window settings |
| `C-c <right>`     | redo window settings |

```
M-x customize-option RET winner-mode RET
```

directional window selection: `windmove` package
```lisp
(windmove-default-keybindings)
```

| Key Binding | Description                       |
| :---------- | :-------------------------------- |
| `S-<left>`  | windmove: move to left window     |
| `S-<right>` | windmove: move to right window    |
| `S-<up>`    | windmove: move to upside window   |
| `S-<down>`  | windmove: move to downside window |

> [!info] Working with Other Windows

The other window: the one immediately after the current one when run `C-x o`.

| Key Binding | Description                                                     |
| :---------- | :-------------------------------------------------------------- |
| `C-x 4 C-f` | find a file in other window                                     |
| `C-x 4 d`   | open `M-x dired` in other window                                |
| `C-x 4 C-o` | display a buffer in other window                                |
| `C-x 4 b`   | switch the buffer in other window and make it the active window |
| `C-x 4 0`   | kill the buffer and window                                      |
| `C-x 4 p`   | run project command in other window                             |

### 5.4.3 Frame Management

Frame: what are called windows in other programs and window managers.

| Key Binding | Description                        |
| :---------- | :--------------------------------- |
| `C-x 5 2`   | create a new frame                 |
| `C-x 5 b`   | switch buffer in other frame       |
| `C-x 5 0`   | delete active frame                |
| `C-x 5 1`   | delete other frames                |
| `C-x 5 C-f` | find a file in other frame         |
| `C-x 5 p`   | run project command in other frame |
| `C-x 5 d`   | open `M-x dired` in other frame    |
| `C-x 5 C-o` | display a buffer in other frame    |

### 5.4.4 Tab Bars and Tab Lines

Since Emacs 27, tow tab modes:
- tab bar mode
- tab line mode

> [!info] Tab Bar Mode

group tabs by **window configuration**: a collection of windows, their sizes, locations, the buffers and so on, that represents a layout of Emacs frame.

```
M-x customize-option RET tab-bar-mode
```

| Key Binding                | Description                           |
| :------------------------- | :------------------------------------ |
| `M-x tab-bar-mode`         | enable tab bar mode                   |
| `C-x t 2`                  | create a new tab                      |
| `C-x t 0`                  | close the current tab                 |
| `C-x t RET`                | select tab by name                    |
| `C-x t o`, `C-<tab>`       | next tab                              |
| `C-S-<tab>`                | previous tab                          |
| `C-x t r`                  | rename tab                            |
| `C-x t m`                  | move tab one position to the right    |
| `C-x t p`                  | run project command in other tab      |
| `C-x t t`                  | execute command in other tab          |
| `C-x t 1`                  | close all other tabs                  |
| `C-x t C-f`, `C-x t f`     | find file in other tab                |
| `C-x t b`                  | switch to buffer in other tab         |
| `C-x t d`                  | open Dired in other tab               |
| `M-x tab-list`             | show an interactive tab list          |
| `M-x tab-auto`             | undo a closed tab for each invocation |
| `M-x tab-recent`           | switch to the last visited tab        |
| `M-x tab-bar-history-mode` | enable tab bar history mode           |

> [!info] Tab Line Mode

a feature more akin to the tabs in a web browser.

| Key Binding                | Description            |
| :------------------------- | :--------------------- |
| `M-x global-tab-line-mode` | enable tab line mode   |
| `C-x <left>`               | select previous buffer |
| `C-x <right>`              | select next buffer     |

### 5.4.5 Elemental Movement

> [!info] Navigation Keys

| Key Binding                                   | Description                                                  |
| :-------------------------------------------- | :----------------------------------------------------------- |
| `<left>`, `<right>`, `<up>`, `<down>`         | arrow keys move by character in 4 directions                 |
| `C-<left>`, `C-<right>`, `C-<up>`, `C-<down>` | arrow keys move by word in 4 directions                      |
| `<insert>`                                    | insert key, activate `overwrite-mode`                        |
| `<delete>`                                    | delete key, delete the character after point                 |
| `<prior>`, `<next>`                           | page up and page down, move up and down nearly one full page |
| `<home>`, `<end>`                             | move to the beginning or end of line                         |

bash, GNU readline-enabled terminal application: by default they use Emacs-style keys.
- `M-f`: move forward by word.

> [!info] Moving by Character

| Key Binding | Description                |
| :---------- | :------------------------- |
| `C-f`       | move forward by character  |
| `C-b`       | move backward by character |

> [!info] Moving by Line

| Key Binding | Description                                                   |
| :---------- | :------------------------------------------------------------ |
| `C-a`       | move point to the beginning of the line                       |
| `C-e`       | move point to the end of the line                             |
| `M-m`       | move point to the first non-whitespace character on this line |
| `C-p`       | move to previous line                                         |
| `C-n`       | move to next line                                             |
screen, logical, visual lines

| Key Binding                             | Description                      |
| :-------------------------------------- | :------------------------------- |
| `M-x customize-option line-move-visual` | use logical lines                |
| `M-x visual-line-mode`                  | use visual lines.                |
| `M-x toggle-truncate-lines`             | toggle word wrapping/truncations |
display line and column numbers:

| Key Binding                                             | Description                                   |
| :------------------------------------------------------ | :-------------------------------------------- |
| `M-x customize-option global-display-line-numbers-mode` | enable line number permanently                |
| `M-x customize-option display-line-numbers-mode`        | enable line number permanently                |
| `M-x customize-group display-line-numbers`              | configure line number counting method         |
| `M-x line-number-mode`                                  | see the current line number the point is on   |
| `M-x column-number-mode`                                | see the current column number the point is on |

> [!info] Moving by Word

| Key Binding | Description           |
| :---------- | :-------------------- |
| `M-f`       | move forward by word  |
| `M-b`       | move backward by word |

**syntax table**: decide the makeup of a word (or symbol, punctuation, comment, etc).
example mode:
- `M-x text-mode`
- `M-x python-mode`

word movement is not symmetric.

| Key Binding          | Description                                           |
| :------------------- | :---------------------------------------------------- |
| `M-x subword-mode`   | minor mode that treat `CamelCase` as distinct words   |
| `M-x superword-mode` | minor mode that treat `snake-case` as one word        |
| `M-x glass-mode`     | visually separate `CamelCase` words into `Camel_Case` |

> [!info] Moving by S-Expressions

s-expression/sexp: balanced expressions
- strings: `"`, `'`
- brackets: `[]`, `()`, `{}`, `<>`

| Key Binding | Description                        |
| :---------- | :--------------------------------- |
| `C-M-f`     | move forward by s-expression       |
| `C-M-b`     | move backward by s-expression      |
| `C-M-d`     | move down into a list - `()`       |
| `C-M-u`     | move up out of a list              |
| `C-M-n`     | move forward to the next list      |
| `C-M-p`     | move backward to the previous list |
| `C-M-k`     | kill the s-expression              |

> [!info] Other Movement Commands

> Moving by Paragraph

| Key Binding | Description                         |
| :---------- | :---------------------------------- |
| `M-}`       | move forward to end of paragraph    |
| `M-{`       | move backward to start of paragraph |

| Variable             | Description                                                          |
| :------------------- | :------------------------------------------------------------------- |
| `paragraph-start`    | define the beginning of a paragraph using a large regular expression |
| `paragraph-separate` | define the paragraph separator as a regular expression               |
| `use-hard-newlines`  | define whether a hard newline defines a paragraph                    |
> Moving by Sentence

| Key Binding | Description                   |
| :---------- | :---------------------------- |
| `M-a`       | move to beginning of sentence |
| `M-e`       | move to end of sentence       |

| Variable                      | Description                                                               |
| :---------------------------- | :------------------------------------------------------------------------ |
| `sentence-end-double-space`   | non-nil means a single space does not end a sentence                      |
| `sentence-end-without-period` | non-nil means a sentence will end without a period                        |
| `sentence-end-without-space`  | a string of characters that end a sentence without requiring spaces after |
> Moving by Defun

| Key Binding | Description                |
| :---------- | :------------------------- |
| `C-M-a`     | move to beginning of defun |
| `C-M-e`     | move to end of defun       |

> Moving by Pages

| Key Binding | Description            |
| :---------- | :--------------------- |
| `C-x ]`     | move forward one page  |
| `C-x [`     | move backward one page |

> [!info] Scrolling

Emacs scrolls by nearly full screens, where a full screen is the number of lines visible in that window.

| Key Binding | Description                                      |
| :---------- | :----------------------------------------------- |
| `C-v`       | scroll down a near full screen                   |
| `M-v`       | scroll up a near full screen                     |
| `C-M-v`     | scroll down the other window                     |
| `C-M-S-v`   | scroll up the other window                       |
| `C-x <`     | scroll left                                      |
| `C-<next>`  | scroll left                                      |
| `C-<prior>` | scroll right                                     |
| `C-x >`     | scroll right                                     |
| `S-<wheel>` | Emacs 28: scroll left/right with the mouse wheel |

| Variable                    | Description                          |
| :-------------------------- | :----------------------------------- |
| `next-screen-context-lines` | retained line numbers when scrolling |

beginning and end of buffer:

| Key Binding | Description                         |
| :---------- | :---------------------------------- |
| `M-<`       | move to the beginning of the buffer |
| `M->`       | move to the end of the buffer       |

### 5.4.6 Bookmarks and Registers

bookmark sources:
- files
- `M-x dired` directories
- `M-x man` pages
- Org mode
- DocView: including PDF files
- into manual pages

bookmark file: `~/.emacs.d/bookmarks`, controlled by varaible `bookmark-default-file`

| Key Binding | Description      |
| :---------- | :--------------- |
| `C-x r m`   | set a bookmark   |
| `C-x r l`   | list bookmarks   |
| `C-x r b`   | jumo to bookmark |

registers are transient, and are single-character store-and-recall mechanisms for several types of data:
- window configurations and framesets
- points
- numbers and text

| Key Binding | Description                            |
| :---------- | :------------------------------------- |
| `C-x r n`   | store number in register               |
| `C-x r s`   | store region in register               |
| `C-x r SPC` | store point in register                |
| `C-x r +`   | increment number in register           |
| `C-x r j`   | jump to register                       |
| `C-x r i`   | insert content of register             |
| `C-x r w`   | store window configuration in register |
| `C-x r f`   | store framesets in register            |

### 5.4.7 Selections and Regions

The **region** is always defined as the contiguous block of text between the **point** and the **mark**.

- `C-<SPC>`: set mark to activate the region.
- press `C-<SPC>` again/`C-g`: deactive the region. 

**TMM(Transient Mark Mode)**: make visual selection

The **mark** in Emacs is not just for the region.
It's a tool for jumping around in a buffer as some commands that whisk you away from our current location will leave a mark on the **mark ring** that you can return to later.
- `M-<`, `M->`: jump to the beginning and end of the buffer.
	- mark the old position before jump
- `C-u C-<SPC>`: return to the old position.

| Key Binding     | Description                                                        |
| :-------------- | :----------------------------------------------------------------- |
| `C-<SPC>`       | set the mark, and toggle the region                                |
| `C-u C-<SPC>`   | jump to the mark, and repeated calls go further back the mark ring |
| `S+<left>`, ... | shift selection similar to other editors                           |
| `C-x C-x`       | exchange the point and mark, and reactivate last region            |

> [!info] Selection Compatibility Modes

| Key Binding                 | Description                                                                            |
| :-------------------------- | :------------------------------------------------------------------------------------- |
| `M-x delete-selection-mode` | delete the selected text first when the region is active and type text into the buffer |
| `M-x cua-mode`              | let you use `C-z`, `C-x`, `C-c` and `C-v` to undo, cut, copy and paste.                |

| Variable            | Description                                                                       |
| :------------------ | :-------------------------------------------------------------------------------- |
| `shift-select-mode` | active the region and extend it in the direction you are moving. default enabled. |

> [!info] Setting the Mark

| Key Binding          | Description                |
| :------------------- | :------------------------- |
| `M-h`                | mark the next paragraph    |
| `C-x h`              | mark the whoe buffer       |
| `C-M-h`              | mark the next defun        |
| `C-x C-p`            | mark the next page         |
| `M-@`                | mark the next word         |
| `C-M-<SPC>`, `C-M-@` | mark the next s-expression |
| `C-<SPC>`, `C-g`     | deactivate the region      |

### 5.4.8 Searching and Indexing

> [!info] Isearch: Increment Search

| Key Binding  | Description                                                        |
| :----------- | :----------------------------------------------------------------- |
| `C-s`        | begin an incremental search                                        |
| `C-r`        | begin a backward incremental search                                |
| `C-M-s`      | begin a regexp incremental search                                  |
| `C-M-r`      | begin a regexp backward incremental search                         |
| `RET`        | pick the selected match: drop a mark at original location          |
| `C-g`        | exit Isearch                                                       |
| `M-<`, `M->` | Emacs 28: jump to first or last match                              |
| `C-v`, `M-v` | Emacs 28: jump to the next or previous match not currently visible |
| `M-n`        | Isearch: move to next item in search history                       |
| `M-p`        | Isearch: move to previous item in search history                   |
| `C-M-i`      | Isearch: TAB-complete search string against previous search string |
| `C-s C-s`    | Isearch: begin Isearch against last search string                  |
| `C-r C-r`    | Isearch: begin bakward Isearch against last search string          |
| `C-w`        | Isearch: add word at point to search string                        |
| `C-M-y`      | Isearch: add character at point to search string                   |
| `M-s C-e`    | Isearch: add rest of line at point to search string                |
| `C-y`        | Isearch: yank/paste from clipboard to search string                |
| `M-s c`      | Isearch: toggle case-sensitivity                                   |
| `M-s r`      | Isearch: toggle regular-expression mode                            |
| `M-s w`      | Isearch: toggle word mode                                          |
| `M-s _`      | Isearch: toggle symbol mode                                        |
| `M-s <SPC>`  | Isearch: toggle lax whitespace matching                            |
| `M-s '`      | Isearch: toggle character folding                                  |
| `M-s .`      | Isearch: forward for symbol at point                               |
| `M-s M-.`    | Isearch: Emacs 28, forward for thing at point                      |
**thing at point**: an extensible system for extracting interesting text around text.

> [!info] Occur: Print and Edit lines matching an expression

a `grep`-like utility built into Emacs.
buffer `*Occur*`

| Key Binding                           | Description                                                                              |
| :------------------------------------ | :--------------------------------------------------------------------------------------- |
| `M-x occur`                           | enable occur mode                                                                        |
| `M-s o`                               | active occur mode globally or on current search string inside Isearch                    |
| `M-n`, `M-p`                          | Occur: go to next and previous occurrence                                                |
| `<`, `>`                              | Occur: go to beginning and end of buffer                                                 |
| `g`                                   | Occur: revert the buffer, refresh the search results                                     |
| `q`                                   | Occur: quit occur mode                                                                   |
| `e`                                   | Occur: switch to occur edit mode                                                         |
| `C-c C-c`                             | Occur: exit occur edit mode and applies changes                                          |
| `M-g M-n`                             | jump to next error                                                                       |
| `M-g M-p`                             | jump to previous error                                                                   |
| `M-x multi-occur-in-matching-buffers` | use the occur mode on multiple buffers, take a regular expression of buffers to match    |
| `M-x multi-occur`                     | use the occur mode on multiple buffers, explicitly select the buffers you want to search |

> [!info] Imenu: Jump to definitions

a generic indexing framework for jumping to points of interest in a buffer.

| Key Binding | Description  |
| :---------- | :----------- |
| `M-x imenu` | invoke imenu |

> [!info] Helm: Incremental Completion and Selection

a generic framework for filter-as-you-type completion
```
M-x package-install RET helm RET
```
prefix key binding: `C-x c`

commands and key bindings: ...

> [!info] IDO: Interactively DO Things

a powerful minibuffer completion engine

IDO is a distraction-free, target aware search
Helm is for in-depth searching and completion

```lisp
(ido-mode 1)
(setq ido-everywhere t)
(setq ido-enable-flex-matching t)
```

key bindings: ...

> [!info] Grep: Searching the file system

mode: `grep-mode`
buffer: `*grep*`

| Key Binding     | Description                                                                      |
| :-------------- | :------------------------------------------------------------------------------- |
| `M-x grep`      | prompt for arguments to pass to `grep`                                           |
| `M-x grep-find` | prompt for arguments to pass to `grep` and `find`                                |
| `M-x lgrap`     | prompt for query and glob pattern to search with `grep`                          |
| `M-x rgrep`     | prompt for query and glob pattern then recursively search with `grep` and `find` |
| `M-x rzgrep`    | like `M-x rgrep` but search compressed gzip files                                |
> Using the Grep Interface

| Key Binding | Description            |
| :---------- | :--------------------- |
| `M-g M-n`   | jump to next match     |
| `M-g M-p`   | jump to previous match |

### 5.4.9 Other Movement Commands

| Key Binding   | Description                                                          |
| :------------ | :------------------------------------------------------------------- |
| `M-r`         | re-position the point to the top left, middle left, or bottom left   |
| `C-l`         | re-center the point to the middle, top, or bottom in the buffer      |
| `C-M-l`       | re-position the comment or definition so it is in view in the buffer |
| `C-x C-n`     | set the goal column, the horizontal position for the point           |
| `C-u C-x C-n` | reset the goal column, the horizontal position for the point         |
| `M-g M-g`     | go to line                                                           |
| `M-g TAB`     | go to column                                                         |
| `M-g c`       | go to character position                                             |

## 5.5 The Theory of Editing

### 5.5.1 Killing and Yanking Text

- **kill** text: cut text in other text editors
- **deleted** text is not retained in the *kill ring*, killed text is.

| Key Binding            | Description                                                 |
| :--------------------- | :---------------------------------------------------------- |
| `C-d`                  | *delete* character                                          |
| `<backspace>`          | *delete* previous character                                 |
| `M-d`, `C-<backspace>` | kill word                                                   |
| `C-k`                  | kill to the end of the line, not kill the newline character |
| `M-k`                  | kill sentence                                               |
| `C-M-k`                | kill s-expression                                           |
| `C-S-<backspace>`      | kill the whole line                                         |

digit argument and negative arguments

| Key Binding   | Description                        |
| :------------ | :--------------------------------- |
| `C-M-3 C-M-k` | kill 3 s-expression                |
| `C-M-- C-M-k` | kill the s-expression before point |

general kill and yank commands:

| Key Binding | Description                                     |
| :---------- | :---------------------------------------------- |
| `C-w`       | kill active region - **cut**                    |
| `M-w`       | copy to the kill ring - **copy**                |
| `C-M-w`     | append to the kill ring                         |
| `C-y`       | yank last kill - **paste**                      |
| `M-y`       | cycle through kill ring, replacing yanked text. |

> [!info] Killing versus Deleting

5 rules of kill commands:
- **consecutive kills append**: all kill commands append to the kill ring, if and only if the last command was also a kill command.
	- break the cycle: move, write, run a command; the next kill command will create a new entry in the kill ring.
- **the kill ring can hold many items**
	- variable `kill-ring-max`
- **the kill ring is global**
	- it's shared between all the buffers in Emacs.
- **killing is also deleting**
- **marking is unnecessary**
	- most of the work involve operations on *syntactic unit*.
	- exceptions: copy the region(`M-w`), kill or copy odd-shaped regions that don't conform to multiples of syntactic units.

> Killing Lines

- `C-S-<backspace>`: kill the whole line
- package `whole-line-or-region`: `C-w` kill the current line the pint if on if the region is not active
- `C-k`: kill to the end of the line
- option `kill-whole-line`: force `C-k` to kill the new line permanently

> [!info] Yanking Text

In Emacs, you **yank** from the kill ring if you want to *paste* text from it.
- insert the current entry in the kill ring at point in the active buffer.
- repeat calls to yank will insert the same text.

| Key Binding | Description                                                                       |
| :---------- | :-------------------------------------------------------------------------------- |
| `C-y`       | yank last kill - **paste**                                                        |
| `M-y`       | cycle through kill ring, replacing yanked text. Emacs 28: show kill ring history. |
cycle through the kill ring:
- press `C-y` where we want the yanked text to appear.
- without moving, editing, executing commands, press `M-y` to step back through the kill ring.

### 5.5.2 Transposing Text

swapping two syntactic units of text with one another.
- first look at where the point is, then swap two syntactic units surrounding the point.
- negative arguments, digit arguments also work.
	- swap the Nth unit ahead of the point with the one immediately before the point.

| Key Binding                | Description             |
| :------------------------- | :---------------------- |
| `C-t`                      | transpose characters    |
| `M-t`                      | transpose words         |
| `C-M-t`                    | transpose s-expressions |
| `C-x C-t`                  | transpose lines         |
| `M-x transpose-paragraphs` | transpose paragraphs    |
| `M-x transpose-sentences`  | transpose sentences     |

> [!info] `C-t`: transpose characters

swap the character to the left and right of the point.
the point move forward one character.

 > [!info] `M-t`: transpose words

cases: plain text, source code.
the point move forward one word.
`M-t` command is intrinsically linked to the `M-x forward`(`M-f`) command.

> [!info] `C-M-t`: transpose e-expressions

`C-M-t` like `M-x forward-sexp`(`C-M-f`), assume the role of `M-x transpose-word` if there are no balanced expressions.

 > [!info] Other Transpose Commands

transpose other syntactic units: lines, paragraphs, sentences.

### 5.5.3 Filling and Commenting

> [!info] Filling

break paragraphs so the lines won't exceed a certain length.

| Key Binding          | Description                                                                                                                                                                                                                  |
| :------------------- | :--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `M-q`                | refill the paragraph.                                                                                                                                                                                                        |
| `C-u M-q`            | refill the paragraph, also justify the text.                                                                                                                                                                                 |
| `C-x f`              | sets the fill column width.                                                                                                                                                                                                  |
| `C-x .`              | set the fill prefix: every character on the current line up to point and make it the fill prefix (insert before the lines when fill a paragraph with `M-q`). remove fill prefix: place point on an empty line, type `C-x .`. |
| `M-x auto-fill-mode` | toggle auto-filling.                                                                                                                                                                                                         |

> [!info] Commenting

| Key Binding       | Description                                               |
| :---------------- | :-------------------------------------------------------- |
| `M-;`             | comment or uncomment DWIM(Do What I Mean).                |
| `C-x C-;`         | comment or uncomment line.                                |
| `M-x comment-box` | comment the region but as a box.                          |
| `M-j`, `C-M-j`    | insert new line and continues with comment on a new line. |

| Key Binding      | Description                                             |
| :--------------- | :------------------------------------------------------ |
| `commnt-style`   | style of comment to use.                                |
| `commnt-styles`  | association list of available comment styles.           |
| `commnt-start`   | character(s) to mark start of comment.                  |
| `commnt-end`     | character(s) to mark end of comment.                    |
| `commnt-padding` | padding used between comment character(s) and the text. |

### 5.5.4 Search and Replace

search: with or without regular expressions.
replace: leverage the power of elisp.

Emacs's regular expression implementation:
- follow the GNU standard for regular expressions.
- different from PCRE(Perl-Compatible Regular Expression)

| Key Binding          | Description                                           |
| :------------------- | :---------------------------------------------------- |
| `C-M-%`              | query regexp search and replace. also inside Isearch. |
| `M-%`                | query search and replace.also inside Isearch.         |
| `M-x replace-string` | search and replace                                    |
| `M-x replace-regexp` | regexp search and replace                             |
**query command**: interactive
- prompts for search and replace.
- the interactive part where we select each match.

options when presented with a match:

| Query Key Binding | Description                        |
| :---------------- | :--------------------------------- |
| `SPC`, `y`        | replace one match, then continue.  |
| `.`               | replace one match, then exit.      |
| `,`               | replace, stay at current match.    |
| `RET`, `q`        | exit without replacing match.      |
| `!`               | replace all matches in buffer.     |
| `^`               | move point back to previous match. |
| `u`, `U`          | undo last/all replacements.        |

> [!info] Case Folding

match string case insensitive unless search for a mixed case or uppercase string.

> [!info] Regular Expressions

missing features:
- negative/positive lookahead or lookbehind
- branch reset group
- `\d`: use `[0-9]` or `[:digit:]` instead.

| Constructs   | Description                                                |
| :----------- | :--------------------------------------------------------- |
| `\|`         | alternative.                                               |
| `\(`, `\)`   | capturing group.                                           |
| `\{`, `\}`   | repetition.                                                |
| `\<`, `\>`   | match beginning and end of word.                           |
| `\_<`, `\_>` | match beginning and end of symbol.                         |
| `\scode`     | match any character whose syntax table code is `code`.     |
| `\Scode`     | match any character whose syntax table code is not `code`. |
syntax classes:
- `-`: whitespace characters
- `w`: word constituents
- `_`: symbol constituents
- `.`: punctuation characters.
- `(`, `)`: open/close parenthesis, `()`, `[]`, `{}`
- `"`: string characters, `'`, `"`
- `<`, `>`: open/close comment characters
example:
- `\s-`
- `\s"`

`C-u M-x waht-cursor-position`, `C-u C-x =`: inspect character's syntax classs. 

> Invoking Elisp

### 5.5.5 Changing Case

### 5.5.6 Counting Things

### 5.5.7 Text Manipulation

> [!info] Editable Occur

> [!info] Deleting Duplicates

> [!info] Flushing and Keeping Lines

> [!info] Copying and Killing Matching Lines

> [!info] Joining and Splitting Lines

> [!info] Whitespace Commands

### 5.5.8 Keyboard Macros

> [!info] Basic Commands

> [!info] Advanced Commands

### 5.5.9 Text Expansion

> [!info] `TAB`: Indenting the Current Line

> [!info] Indenting Regions

### 5.5.10 Indenting Text and Code

> [!info] `TAB`: Indenting the Current Line

> [!info] Indenting Regions

### 5.5.11 Sorting and Aligning

> [!info] Sorting

> [!info] Aligning

### 5.5.12 Other Editing Commands

> [!info] Zapping Characters

> [!info] Spell Checking

> [!info] Quoted Insert

## 5.6 The Practicals of Emacs

**workflow**: walkthroughs that cover a specific area or problem in some depth.

### 5.6.1 Exploring Emacs
> [!tip] To truly master Emacs, you have to learn how to find things.

> [!info] Reading the Manual

> [!info] Using Apropos

> [!info] `C-h`: Exploring prefix keys

> [!info] `C-h k`: Describe what a key does

> [!info] `C-h m`: Finding more commands

> [!info] `M-S-x`: Execute extended command for buffer

### 5.6.2 Project Management

### 5.6.3 Xref: Cross-References in Emacs

### 5.6.4 Working with Log Files

> [!info] Browsing Other Files

### 5.6.5 TRAMP: Remote File Editing

> [!info] The Default Directory and Remote Editing

> [!info] Multi-Hops and User Switching

### 5.6.6 EWW: Emacs Web Wowser

### 5.6.7 Dired: Files and Directories

Emacs's directory editor: dired.

Access dired:
- IDO or FIDO mode: when `C-x C-f`, type`C-d`.
- `M-x dired`: `default-directory` the directory the current buffer is in.
- `C-x d`: same as above.
- `C-x 4 d`: in the other window.

customize: `dired-listing-switches`.
`dired-mode`

> [!info] Navigation

| Key Binding            | Description                      |
| :--------------------- | :------------------------------- |
| `RET`                  | visit the fire or directory      |
| `^`                    | go up one directory              |
| `q`                    | quit dired                       |
| `n`, `p`, `C-n`, `C-p` | move the point up/down a listing |

> [!info] Marking and Unmarking

operations on multiplie files or directories.

| Key Binding | Description        |
| :---------- | :----------------- |
| `m`         | mark active        |
| `u`         | unmark active      |
| `U`         | unmark everything  |
| `d`         | flags for deletion |
- `D` flags for deletion
- `*` highlight marked files.

| Key Binding | Description             |
| :---------- | :---------------------- |
| `* m`       | mark region             |
| `* u`       | unmark region           |
| `* %`       | mark files by regexp    |
| `* .`       | mark files by extension |
| `t`, `* t`  | toggle marking          |
| `* c`       | change mark             |

> [!info] Operations

operations on
- active item (if there are no marked files in dired).
- marked item: ask you to confirm, list the affected files.

| Key Binding(Marked files) | Description                  |
| :------------------------ | :--------------------------- |
| `C`                       | copy files                   |
| `R`                       | rename or move files         |
| `O`                       | change owner                 |
| `G`                       | change group                 |
| `M`                       | change permission            |
| `D`                       | delete marked                |
| `x`                       | delete flaged                |
| `F`                       | visit files: require dired-x |
| `c`                       | compress marked to a file    |

| Key Binding | Description                 |
| :---------- | :-------------------------- |
| `g`         | refresh dired buffer        |
| `+`         | create a subdirectory       |
| `s`         | toggle sorting by name/date |
| `<`, `>`    | jump to prev/next directory |
| `j`         | jump to file                |

> Dired-X
```lisp
(require 'dired-x)
```

| Key Binding | Description                                          |
| :---------- | :--------------------------------------------------- |
| `F`         | visit all marked files, open each file in new window |
| `C-u F`     | visit all marked files, open them in the background  |

search through or replace text in files: multi-file Isearch

| Key Binding(Marked files) | Description                                                |
| :------------------------ | :--------------------------------------------------------- |
| `M-s a C-s`               | begin isearch                                              |
| `Q`                       | xref query replace regexp: call `C-M-%`                    |
| `A`                       | xref search by regexp                                      |
| `!`                       | synchronous shell command: buffer `*Shell Command Output*` |
| `&`                       | asynchronous shell command: buffer `*Async Shell Command*` |
variable `dired-guess-shell-alist-default`

with active marks, `!` and `&` will call out to an external command of your choice:
- one command per marked item: `?`
- one command for all marked items: `*`

> [!info] Working Across Directories

- `i` with point on a directory: insert the directory in the same dired buffer as a sub-directory.
- `$`: collapse a sub-directory, commands won't apply to it.

Emacs's `find` wrapper commands: take the output of `find` and build a dired buffer relative to a starting directory.

| Key Binding                | Description                        |
| :------------------------- | :--------------------------------- |
| `M-x find-dired`           | call `find` with a pattern         |
| `M-x find-name-dired`      | call `find` with `-name`           |
| `M-x find-grep-dired`      | call `find` and `grep`             |
| `M-x find-lisp-find-dired` | Use Emacs and regexp to find files |

### 5.6.8 Shell Commands

shell command work on generic buffers:

| Key Binding | Description                                        |
| :---------- | :------------------------------------------------- |
| `M-!`       | call shell commands and prints outputs             |
| `C-u M-!`   | call shell commands and insert outputs into buffer |
| `M-&`       | like `M-!` but asynchronous                        |
| `C-u M-&`   | like `C-u M-!` but asynchronous                    |
| `M-\|`      | pipe region to shell command                       |
| `C-u M-\|`  | like `M-\|` but replace region                     |

> [!info] Compiling in Emacs

| Key Binding          | Description                                 |
| :------------------- | :------------------------------------------ |
| `M-x compile`        | run a command, track errors. default `make` |
| `M-x recompile`      | re-run last command                         |
| `M-g M-n`, `M-g M-p` | jump to next/previous error                 |
| `g`                  | re-run last command                         |
| `C-x p c`            | compile in the current project              |

### 5.6.9 Shells in Emacs

| Key Binding     | Description                                            |
| :-------------- | :----------------------------------------------------- |
| `M-x shell`     | a simple wrapper around an external shell, like `bash` |
| `M-x eshell`    | a complete shell implementation written in elisp       |
| `M-x ansi-term` | a terminal emulator                                    |

> [!info] `M-x shell`: Shell Mode

| Key Binding          | Description                      |
| :------------------- | :------------------------------- |
| `M-p`, `M-n`         | cycle through command history    |
| `C-<up>`, `C-<down>` | cycle through command history    |
| `M-r`                | ISearch history backward         |
| `C-c C-p`, `C-c C-n` | jump to previous/next prompt     |
| `C-c C-s`            | save command output to file      |
| `C-c C-o`            | kill command output to kill ring |
| `C-c C-l`            | list command history             |
| `C-d`                | delete forward char or send `^D` |
| `C-c C-z`            | send stop sub job                |
| `TAB`                | complete at the point            |

> [!info] `M-x ansi-term`: Terminal Emulator

| Key Binding | Description                                                        |
| :---------- | :----------------------------------------------------------------- |
| `C-c C-j`   | switch to line mode: like a typical Emacs buffer                   |
| `C-c C-k`   | switch to character mode(default): like a normal terminal emulator |

> [!info] `M-x eshell`: Emacs's Shell

Every command type into Eshell is:
- first filtered through Eshell's own emulation layer, 
- then through Emacs's own interactive commands, 
- and then finally through programs in `$PATH` or in the current directory.
ex:
- `dired .`: open `M-x dired` session in the current directory.
- `find-file todo.org`: open `todo.org` in currently-running Emacs.

## 5.7 Conclusion

How do you master a text editor as diverse as Emacs?
The answer: by knowing how to ask it the right questions.

Emacs is no longer an opaque box but a very open and transparent one that we can peer into, modify and observe the results of those changes.

The natural next step is learn elisp.

### 5.7.1 Other Resources

> [!info] Third-Party Packages and Tools

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

> [!info] Communities

- Reddit: `/r/emacs`, `/r/orgmode`
- StackExchage: https://emacs.stackexchange.com/
- Blogs

| Blog                    | Link                                     |
| :---------------------- | :--------------------------------------- |
| Mastring Emacs          | https://www.masteringemacs.org/          |
| Sacha Chua              | https://sachachua.com/blog/              |
| Irreal’s Emacs blog     | https://irreal.org/blog/                 |
| Artur Malabarba         | https://endlessparentheses.com/          |
| Bozhidar Batzov         | https://batsov.com/                      |
| John Kitchin            | https://kitchingroup.cheme.cmu.edu/blog/ |
| Planet Emacs aggregator | https://planet.emacslife.com/            |
- Emacs

# 6 总结

<!-- 概要记录书籍中如何解决关键性问题的. -->

# 7 应用

<!-- 记录如何使用书籍中方法论解决你自己的问题. -->

# 8 文献引用

<!-- 记录相关的和进一步阅读资料: 文献、网页链接等. -->
- [Home](https://www.masteringemacs.org/)

- [The quick brown fox jumps over the lazy dog - wikipedia](https://en.wikipedia.org/wiki/The_quick_brown_fox_jumps_over_the_lazy_dog): an English-language pangram – a sentence that contains all the letters of the alphabet.

# 9 其他备注
- [Evaluating Elisp in Emacs](https://www.masteringemacs.org/article/evaluating-elisp-emacs)


## 9.1 GNU Texinfo
- [Home](https://www.gnu.org/software/texinfo/)
## 9.2 XDG(X Desktop Group)
- [XDG Base Directory Specification](https://specifications.freedesktop.org/basedir-spec/latest/): version 0.8, 2021.
- abbrev: [Doom and XDG directories](https://discourse.doomemacs.org/t/doom-and-xdg-directories/3012)
## 9.3 apropos
- [apropos (Unix) - wikipedia](https://en.wikipedia.org/wiki/Apropos_(Unix)): apropos is a command to search the man page files in Unix and Unix-like operating systems.
## 9.4 Keys
Super:
- [Make use of the Super key](https://emacsredux.com/blog/2013/07/17/make-use-of-the-super-key/)
- [lowercase `s` as prefix in `describe-bindings`](https://emacs.stackexchange.com/questions/76385/lowercase-s-as-prefix-in-describe-bindings)
## 9.5 IDO, FIDO
- [Introduction to IDO mode](https://www.masteringemacs.org/article/introduction-to-ido-mode)