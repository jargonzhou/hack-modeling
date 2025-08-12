# Doom Emacs
- https://github.com/doomemacs/doomemacs
- [Doom Emacs Documentation](https://docs.doomemacs.org/latest/): 2024-09-16 not complete.

> Doom is a configuration framework for [GNU Emacs](https://www.gnu.org/software/emacs/) tailored for Emacs bankruptcy veterans who want less framework in their frameworks, a modicum of stability (and reproducibility) from their package manager, and the performance of a hand rolled config (or better). It can be a foundation for your own config or a resource for Emacs enthusiasts to learn more about our favorite operating system.


# Concepts

## Official modules
- [Code and Doc](https://github.com/doomemacs/doomemacs/tree/master/modules)

Module list (150)

| Module       | Count | Description                                                                                                                                                                                                         |
| :----------- | :---- | :------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `app`        | 6     | Application modules are complex and opinionated modules that transform Emacs toward a specific purpose. They may have additional dependencies and should be loaded last (but before `doom-module::config modules`). |
| `checkers`   | 3     | For modules dedicated to linting plain text (primarily code and prose).                                                                                                                                             |
| `completion` | 5     | These modules provide interfaces and frameworks completion, including code completion.                                                                                                                              |
| `config`     | 2     | Modules in this category provide sane defaults or improve your ability to configure Emacs. It is best to load these last.                                                                                           |
| `editor`     | 12    | For modules concerned with the insertion and editing of text. Amen.                                                                                                                                                 |
| `emacs`      | 6     | Modules in this category augment and extend the built-in features of Emacs.                                                                                                                                         |
| `email`      | 3     | Modules that turn Emacs in an email client.                                                                                                                                                                         |
| `input`      | 3     | Modules in this category extend Emacs support for additional keyboard layouts and input methods for non-English languages.                                                                                          |
| `lang`       | 60    | These modules specialize in integration particular languages and their ecosystems into (Doom) Emacs.                                                                                                                |
| `os`         | 2     | Modules in this category are designed to improve compatibility with certain operating systems or OS features (like the shell).                                                                                      |
| `term`       | 4     | What’s an operating system without a terminal? The modules in this category bring varying degrees of terminal emulation into Emacs.                                                                                 |
| `tools`      | 21    | Modules that integrate external tools into Emacs.                                                                                                                                                                   |
| `ui`         | 23    | For modules concerned with changing Emacs’ appearance or providing interfaces for its features, like sidebars, tabs, or fonts.                                                                                      |

## `:editor format`
This module integrates code formatters into Emacs. 
Here are some of the formatters that it currently supports:
> asmfmt, black, brittany, cabal-fmt, clang-format, cmake-format, dartfmt, dfmt, dhall format, dockfmt, elm-format, emacs, fish_indent, fprettify, gleam format, gofmt, iStyle, jsonnetfmt, ktlint, latexindent, ledger-mode, lua-fmt, mix format, nixfmt, node-cljfmt, ocp-indent, perltidy, prettier, purty, rufo, rustfmt, scalafmt, script shfmt, snakefmt, sqlformat, styler, swiftformat, tidy

## ## `:editor snippets`
This module adds snippet expansions to Emacs, powered by `doom-package:yasnippet`.

## `:lang common-lisp`
- [SLIME/SBCL integration #1542](https://github.com/doomemacs/doomemacs/issues/1542)
> Doom has a `:lang common-lisp` module. ... It uses [sly](https://github.com/joaotavora/sly), rather than slime, however (a better fork of slime).
- [Why this "keybinding conflicts" message keeps appearing? How can I fix it?](https://emacs.stackexchange.com/questions/65022/why-this-keybinding-conflicts-message-keeps-appearing-how-can-i-fix-it)
> [sly] SLIME detected in 'lisp-mode-hook', causes keybinding conflicts. Remove it for this Emacs session?
> ...
> Both SLIME and SLY are user interfaces for interacting with a running Lisp process. SLY is much newer than SLIME, and so it copies some conventions and key bindings from SLIME. You can’t usefully use both at the same time, so the author of SLY made it check to see if you have SLIME configured as well.

## `:term vterm`
This module provides a terminal emulator powered by libvterm. It is still in alpha and requires a component be compiled (`vterm-module.so`).

## `:tools lsp`
This module integrates [language servers](https://langserver.org/) into Doom Emacs. They provide features you’d expect from IDEs, like code completion, realtime linting, language-aware `doom-package:imenu`/`doom-package:xref` integration, jump-to-definition/references support, and more.

- [rust](https://docs.doomemacs.org/v21.12/modules/lang/rust/): [[index.Rust#6.8 Emacs mode rustic]]

## `:tools magit`
This module provides Magit, an interface to the Git version control system.

## `:tools tree-sitter`
This module adds [tree-sitter](https://tree-sitter.github.io/tree-sitter/) support to Doom Emacs.

> Tree sitter is a parser generator tool and an incremental parsing library. It can build a concrete syntax tree for a source file and efficiently update the syntax tree as the source file is edited. This allows for features of the editor to become syntax aware.

## `:ui treemacs`

> Treemacs is a file and project explorer similar to NeoTree or vim’s NerdTree, but largely inspired by the Project Explorer in Eclipse. It shows the file system outlines of your projects in a simple tree layout allowing quick navigation and exploration, while also possessing basic file management utilities.



# Usage

## Installation
MacOS dependency:
```shell
# required dependencies
# ripgrep: install using Rust, https://github.com/BurntSushi/ripgrep
brew install git ripgrep
# optional dependencies
brew install coreutils fd
# Installs clang
xcode-select --install
```

install:
```shell
git clone --depth 1 https://github.com/doomemacs/doomemacs ~/.config/emacs
~/.config/emacs/bin/doom install

export PATH="/Users/zhang/.config/emacs/bin:$PATH"
```

uninstall: [How to uninstall doom emacs?](https://www.reddit.com/r/emacs/comments/fam1mo/how_to_uninstall_doom_emacs/)
```shell
rm -rf .config/doom
rm -rf .config/emacs
rm -rf ~/.emacs
rm -rf ~/.emacs.d
rm -rf ~/.doom
rm -rf ~/.doom.d
```

## Commands
- `doom sync` to synchronize your private config with Doom by installing missing packages, removing orphaned packages, and regenerating caches. Run this whenever you modify your private `init.el` or `packages.el`, or install/remove an Emacs package through your OS package manager (e.g. mu4e or agda).
- `doom upgrade` to update Doom to the latest release & all installed packages.
- `doom doctor` to diagnose common issues with your system and config.
- `doom env` to dump a snapshot of your shell environment to a file that Doom will load at startup. This allows Emacs to inherit your `PATH`, among other things.

## Configuration
paths: [ref](https://github.com/doomemacs/doomemacs/blob/master/docs/getting_started.org#configure)
- `~/.config/doom`
	- `init.el`: `doom!` block
	- `config.el`: most private configuration
	- `packages.el`: package management `package!`
	- `custom.el`
- `~/.config/emacs`

## `~/.config/doom`
```shell
➜  doom tree ~/.config/doom 
~/.config/doom
├── config.el
├── custom.el
├── init.el
└── packages.el
```

## `~/.config/emacs`
```shell
➜  emacs git:(master) tree -d ~/.config/emacs
```


## Key Bindins
> [!warning] NOT USE evil!!!
- `SPC h` => `C-h`
- `C-h b b`: explore all key bindings
- `C-h k`: describe a command of a keybinding
- `C-h f`: describe a function
- `C-h v`: describe a variable


- `C-c f P`: open private configuration
- `C-c h t`: choose a theme - `doom-zenburn`


# FAQ
- [Modules are loaded in reverse order, causing breakage and lost keybindings #8055](https://github.com/doomemacs/doomemacs/issues/8055)
```shell
# Error in a Doom module: modules/config/default/+evil-bindings.el, (void-variable evil-window-map)
doom sync -u
```
- [Icons not loading correctly on doom start page, dired, modeline. Fonts are installed properly. #7379](https://github.com/doomemacs/doomemacs/issues/7379)
```
M-x package-install RET nerd-icons RET
M-x nerd-icons-install-fonts
```
- [Cannot open load file: straight.el error on doom install #6346](https://github.com/doomemacs/doomemacs/issues/6346)
```
# delete ~/.emacs.d/local
doom install
```
- [How to disable evil-mode everywhere?](https://emacs.stackexchange.com/questions/53319/how-to-disable-evil-mode-everywhere)
turn off evil: `~/.config/doom/init.el`
```
:editor
;;(evil +everywhere)
```


# See Also
- [Getting Started with Doom Emacs](https://aquabeam.me/tech/doom_emacs_intro/): a tutorial
	- Installation
	- First Moments: projects, getting help + discovery
	- Understanding Your Config: `init.el`, `config.el`, `package.el`
	- Turn Emacs into an IDE: languages, `lsp`, `tree-sitter`, `vterm`, `treemacs`, Magit
	- General tips: managing windows, workspaces
> It also provides (optional) vim emulation powered by [`evil-mode`](https://github.com/emacs-evil/evil) out of the box, so if you’re comfortable with vim keybindings, you’ll feel right at home.
- [My Doom Emacs configuration, with commentary](https://zzamboni.org/post/my-doom-emacs-configuration-with-commentary/): config example, 2021-11-05.
- [Migrating To Doom Emacs](https://blog.jethro.dev/posts/migrating_to_doom_emacs/): migrate example, 2020-03-15. 
> Doom starts out with a configuration using `evil-mode` everywhere.