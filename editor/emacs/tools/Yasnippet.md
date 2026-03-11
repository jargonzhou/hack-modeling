# Yasnippet: Yet another snippet extension
* [Yasnippet - EmacsWiki](https://www.emacswiki.org/emacs/Yasnippet)
* https://joaotavora.github.io/yasnippet/

> Yasnippet
> **YASnippet** is a template system for Emacs. It allows you to type an abbreviation and automatically expand it into function templates. Bundled language templates include: C, C++, C#, Perl, Python, Ruby, SQL, LaTeX, HTML, CSS and more. The snippet syntax is inspired from [TextMate's](http://manual.macromates.com/en/snippets) syntax, you can even [import](https://github.com/joaotavora/yasnippet#import) most TextMate templates to YASnippet. Watch [a demo on YouTube](http://www.youtube.com/watch?v=ZCGmZK4V7Sg).

```
M-x package-install RET yasnippet RET
```
``` lisp
(require 'yasnippet)
(yas-global-mode 1)
```

# Doc
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
* [YASnippet menu](https://joaotavora.github.io/yasnippet/snippet-menu.html)
* [Writing snippets](https://joaotavora.github.io/yasnippet/snippet-development.html)
