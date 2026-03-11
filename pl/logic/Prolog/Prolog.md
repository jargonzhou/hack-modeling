# Prolog
* https://en.wikipedia.org/wiki/Prolog

> Prolog is a logic programming language that has its origins in artificial intelligence, automated theorem proving and computational linguistics.
> 
> Prolog has its roots in first-order logic, a formal logic, and unlike many other programming languages, Prolog is intended primarily as a declarative programming language: the program is a set of facts and rules, which define relations. A computation is initiated by running a query over the program.
> Prolog was one of the first logic programming languages and remains the most popular such language today, with several free and commercial implementations available. The language has been used for theorem proving, expert systems, term rewriting, type systems, and automated planning, as well as its original intended field of use, natural language processing.
> 
> Prolog is a Turing-complete, general-purpose programming language, which is well-suited for intelligent knowledge-processing applications.

Materials
* Declarative Logic Programming- Theory, Systems, and Applications, 2018
* Datalog and Logic Database
* R. A. O’Keefe. The Craft of Prolog. MIT Press, Massachussetts, 1990.
* Programming in Prolog- Using the ISO Standard, 2003

# Tools
## SWI-Prolog
* https://www.swi-prolog.org/
* A Jupyter Kernel for SWI-Prolog: https://github.com/targodan/jupyter-swi-prolog
* SWISH: https://swish.swi-prolog.org/
* SWISH: SWI-Prolog for sharing: https://arxiv.org/abs/1511.00915

## GNU Prolog
* http://www.gprolog.org/
* https://github.com/didoudiaz/gprolog


- GNU Prolog: 下载后默认安装在目录`/opt/local/bin/gprolog`
- Emacs: prolog-mode

`~/.bash_profile`(NOT WORK):

``` shell
# Prolog
export PATH=/opt/local/bin:$PATH
export EPROLOG=/opt/local/bin/gprolog
```

`~/.emacs`(WORK):

``` lisp
;;; Prolog
; cannot find program error: https://askubuntu.com/questions/65168/emacs-24-cant-find-ls
; /opt/local/bin/gprolog
(setenv "PATH" (concat (getenv "PATH") ":/opt/local/bin/"))
(setq exec-path (append exec-path '("/opt/local/bin/")))

; https://www.emacswiki.org/emacs/PrologMode
; https://bruda.ca/emacs/prolog_mode_for_emacs
; https://github.com/emacs-mirror/emacs/blob/master/lisp/progmodes/prolog.el
(autoload 'run-prolog "prolog" "Start a Prolog sub-process." t)
(autoload 'prolog-mode "prolog" "Major mode for editing Prolog programs." t)
(autoload 'mercury-mode "prolog" "Major mode for editing Mercury programs." t)
(setq prolog-system 'gnu)
(setq auto-mode-alist (append '(("\\.pl$" . prolog-mode)
                                ("\\.m$" . mercury-mode))
                               auto-mode-alist))
```