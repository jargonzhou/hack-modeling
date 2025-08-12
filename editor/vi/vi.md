# vi, Vim
* [vi (text editor) - wikipedia](https://en.wikipedia.org/wiki/Vi_(text_editor))
* [Vim (text editor)](https://en.wikipedia.org/wiki/Vim_(text_editor))
	- [Vim - the ubiquitous text editor](https://www.vim.org/)
	- [Code](https://github.com/vim/vim)

> Vim - the ubiquitous text editor
>
> Vim is a highly configurable text editor built to make creating and changing any kind of text very efficient. It is included as "vi" with most UNIX systems and with Apple OS X.
> 
> Vim is rock stable and is continuously being developed to become even better. Among its features are:
> - persistent, multi-level undo tree
> - extensive plugin system
> - support for hundreds of programming languages and file formats
> - powerful search and replace
> - integrates with many tools

books:
* https://iccf-holland.org/vim_books.html
* Learning the vi and Vim Editors, 2021

# Introduction
* [An introduction to the vi editor](https://www.redhat.com/sysadmin/introduction-vi-editor) - 2019-08-20
	- [Linux basics: A beginner's guide to text editing with vim](https://www.redhat.com/sysadmin/beginners-guide-vim) - 2019-10-23
> Vi is often a symbolic link to [Vim](https://www.redhat.com/sysadmin/beginners-guide-vim) (Vi Improved) or an alias to Vim, an enhanced version of Vi.
```shell
➜  ~ ls -al `which vi`
lrwxr-xr-x  1 root  wheel  3 Nov  7  2020 /usr/bin/vi -> vim
```

# Shortcuts
Cheat Sheet:
* https://www.atmos.albany.edu/daes/atmclasses/atm350/vi_cheat_sheet.pdf
* https://web.mit.edu/merolish/Public/vi-ref.pdf
* https://www2.seas.gwu.edu/~mems/ece215/reference/vi-cheatsheet.pdf
* https://gist.github.com/AaronPhalen/99d84494dfd36523c0de

| Key           | Description                                         |
| :------------ | :-------------------------------------------------- |
| `i`           | Switch to Insert mode.                              |
| `ESC`         | Switch to Command mode.                             |
| `:w`          | Save and continue editing.                          |
| `:wq`, `ZZ`   | Save and quit/exit vi.                              |
| `:q!`         | Quit vi and do not save changes.                    |
| `yy`          | Yank (copy) a line of text.                         |
| `p`           | Paste a line of yanked text below the current line. |
| `o`           | Open a new line under the current line.             |
| `O`           | Open a new line above the current line.             |
| `A`           | Append to the end of the line.                      |
| `a`           | Append after the cursor's current position.         |
| `I`           | Insert text at the beginning of the current line.   |
| `b`           | Go to the beginning of the word.                    |
| `e`           | Go to the end of the word.                          |
| `x`           | Delete a single character.                          |
| `dd`          | Delete an entire line.                              |
| `Xdd`         | Delete X number of lines.                           |
| `Xyy`         | Yank X number of lines.                             |
| `G`           | Go to the last line in a file.                      |
| `XG`          | Go to line X in a file.                             |
| `gg`          | Go to the first line in a file.                     |
| `:num`        | Display the current line’s line number.             |
| `h`           | Move left one character.                            |
| `j`           | Move down one line.                                 |
| `k`           | Move up one line.                                   |
| `l`           | Move right one character.                           |
| `:set number` | Show line numbers                                   |

# Search and Replace
* [How to Search in Vim / Vi](https://linuxize.com/post/vim-search/) - 2020-10-02
* [Searching and Replacing With vi](https://docs.oracle.com/cd/E19253-01/806-7612/editorvi-62/index.html)

| Key                                        | Description                            |
| :----------------------------------------- | -------------------------------------- |
| `/`                                        | search forward                         |
| `?`                                        | search backward                        |
| `RET`                                      | run search                             |
| `n`                                        | next occurrence                        |
| `N`                                        | previous occurrence                    |
| `*`                                        | search current word forward            |
| `#`                                        | search current word backward           |
| `/` ↑, `?` ↑                               | search history backward                |
| `/` ↓, `?` ↓                               | search history forward                 |
| `:set ignorecase`, `:set ic`               | search without case sensitivity        |
| `:set noignorecase`, `:set noic`           | search with case sensitivity (default) |
| `:g/[search-string]/s//[replace-string]/g` | search and replace                     |
| `:%s/[search-string]/[replace-string]/g`   | search and replace                     |

# FAQ
* [How do you search through Vim's command history?](https://stackoverflow.com/questions/741913/how-do-you-search-through-vims-command-history)
```shell
# in normal mode
q:
```