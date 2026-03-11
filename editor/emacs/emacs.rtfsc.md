# Emacs Code
* https://github.com/emacs-mirror/emacs
* https://www.gnu.org/savannah-checkouts/gnu/emacs/download.html

subdirectories
- `src`: holds the **C code for Emacs** (the Emacs Lisp interpreter and its primitives, the redisplay code, and some basic editing functions).
- `lisp`: holds the **Emacs Lisp code for Emacs** (most everything else).
- `leim`: holds the original source files for the generated files in lisp/leim.  These form the library of **Emacs input methods**, required to type international characters that can't be directly produced by your keyboard.
- `lib`: holds source code for libraries used by Emacs and its utilities
- `lib-src`: holds the source code for some utility programs for use by or with Emacs, like movemail and etags.
- `lwlib`: holds the sources of the Lucid Widget Library used on X.
- `oldXMenu`: source files from X11R2 XMenu library, used in non-toolkit builds.
- `etc`: holds miscellaneous architecture-independent data files Emacs uses, like the tutorial text and tool bar images. The contents of the 'lisp', 'leim', 'info', and 'doc' subdirectories are architecture-independent too.
- `info`: holds the Info documentation tree for Emacs.
- `doc/emacs`: holds the source code for the Emacs Manual.  If you modify the manual sources, you will need the 'makeinfo' program to produce an updated manual.  'makeinfo' is part of the GNU Texinfo package; you need a suitably recent version of Texinfo.
- `doc/lispref`: holds the source code for the Emacs Lisp reference manual.
- `doc/lispintro`: holds the source code for the Introduction to Programming in Emacs Lisp manual.
- `msdos`: holds configuration files for compiling Emacs under MS-DOS.
- `nextstep`: holds instructions and some other files for compiling the Nextstep port of Emacs, for GNUstep and macOS Cocoa.
- `nt`: holds code and documentation for building Emacs on MS-Windows.
- `test`: holds **tests** for various aspects of Emacs's functionality.
- `modules`: holds the modhelp.py helper script.
- `admin`: holds files used by Emacs developers, and Unicode data files.
- `build-aux`: holds auxiliary files used during the build.
- `m4`: holds Autoconf macros used for generating the configure script.
- `java`: holds the Java code for the Emacs port to Android.
- `cross`: holds Makefiles and an additional copy of gnulib used to build Emacs for Android devices.
- `exec`: holds the source code to several helper executables used to run user-installed programs on Android.

# lisp

```shell
├── calc
├── calendar
├── cedet
│   ├── ede
│   ├── semantic
│   │   ├── analyze
│   │   ├── bovine
│   │   ├── decorate
│   │   ├── symref
│   │   └── wisent
│   └── srecode
├── emacs-lisp
├── emulation
├── erc
├── eshell
├── gnus
├── image
├── international
├── language
├── leim
│   ├── ja-dic
│   └── quail
├── mail
├── mh-e
├── net
├── nxml
├── obsolete
├── org
├── play
├── progmodes
├── term
├── textmodes
├── url
├── use-package
└── vc
```

```shell
├── abbrev.el
├── align.el
├── allout.el
├── allout-widgets.el
├── ansi-color.el
├── ansi-osc.el
├── apropos.el
├── arc-mode.el
├── array.el
├── auth-source.el
├── auth-source-pass.el
├── autoinsert.el
├── autorevert.el
├── avoid.el
├── battery.el
├── bindings.el
├── bind-key.el
├── bookmark.el
├── bs.el
├── buff-menu.el
├── button.el
├── calculator.el
├── case-table.el
├── cdl.el
├── char-fold.el
├── chistory.el
├── cmuscheme.el
├── color.el
├── comint.el
├── completion.el
├── completion-preview.el
├── composite.el
├── cus-dep.el
├── cus-edit.el
├── cus-face.el
├── cus-load.el
├── cus-start.el
├── cus-theme.el
├── custom.el
├── dabbrev.el
├── delim-col.el
├── delsel.el
├── descr-text.el
├── desktop.el
├── dframe.el
├── dired-aux.el
├── dired.el
├── dired-loaddefs.el
├── dired-x.el
├── dirtrack.el
├── display-fill-column-indicator.el
├── display-line-numbers.el
├── disp-table.el
├── dnd.el
├── doc-view.el
├── dom.el
├── dos-fns.el
├── dos-vars.el
├── dos-w32.el
├── double.el
├── dynamic-setting.el
├── ebuff-menu.el
├── echistory.el
├── ecomplete.el
├── editorconfig-conf-mode.el
├── editorconfig-core.el
├── editorconfig-core-handle.el
├── editorconfig.el
├── editorconfig-fnmatch.el
├── editorconfig-tools.el
├── edmacro.el
├── ehelp.el
├── elec-pair.el
├── electric.el
├── elide-head.el
├── emacs-lock.el
├── env.el
├── epa-dired.el
├── epa.el
├── epa-file.el
├── epa-hook.el
├── epa-ks.el
├── epa-mail.el
├── epg-config.el
├── epg.el
├── eshell
├── expand.el
├── external-completion.el
├── ezimage.el
├── facemenu.el
├── face-remap.el
├── faces.el
├── ffap.el
├── filecache.el
├── fileloop.el
├── filenotify.el
├── files.el
├── filesets.el
├── files-x.el
├── find-cmd.el
├── find-dired.el
├── finder.el
├── finder-inf.el
├── find-file.el
├── find-lisp.el
├── flow-ctrl.el
├── foldout.el
├── follow.el
├── font-core.el
├── font-lock.el
├── format.el
├── format-spec.el
├── forms.el
├── frame.el
├── frameset.el
├── fringe.el
├── generic-x.el
├── help-at-pt.el
├── help.el
├── help-fns.el
├── help-macro.el
├── help-mode.el
├── hexl.el
├── hex-util.el
├── hfy-cmap.el
├── hilit-chg.el
├── hi-lock.el
├── hippie-exp.el
├── hl-line.el
├── htmlfontify.el
├── ibuf-ext.el
├── ibuffer.el
├── ibuffer-loaddefs.el
├── ibuf-macs.el
├── icomplete.el
├── ido.el
├── ielm.el
├── iimage.el
├── image.el
├── image-file.el
├── image-mode.el
├── imenu.el
├── indent-aux.el
├── indent.el
├── info.el
├── info-look.el
├── informat.el
├── info-xref.el
├── isearchb.el
├── isearch.el
├── jit-lock.el
├── jka-cmpr-hook.el
├── jka-compr.el
├── json.el
├── jsonrpc.el
├── kermit.el
├── keymap.el
├── kmacro.el
├── ldefs-boot.el
├── loaddefs.el
├── loadhist.el
├── loadup.el
├── locate.el
├── lpr.el
├── ls-lisp.el
├── macros.el
├── man.el
├── master.el
├── mb-depth.el
├── md4.el
├── menu-bar.el
├── midnight.el
├── minibuf-eldef.el
├── minibuffer.el
├── misc.el
├── misearch.el
├── mouse-copy.el
├── mouse-drag.el
├── mouse.el
├── mpc.el
├── msb.el
├── mwheel.el
├── newcomment.el
├── notifications.el
├── novice.el
├── obarray.el
├── outline.el
├── paren.el
├── password-cache.el
├── pcmpl-cvs.el
├── pcmpl-git.el
├── pcmpl-gnu.el
├── pcmpl-linux.el
├── pcmpl-rpm.el
├── pcmpl-unix.el
├── pcmpl-x.el
├── pcomplete.el
├── pgtk-dnd.el
├── pixel-scroll.el
├── plstore.el
├── printing.el
├── proced.el
├── profiler.el
├── ps-bdf.el
├── ps-mule.el
├── ps-print.el
├── ps-print-loaddefs.el
├── ps-samp.el
├── recentf.el
├── rect.el
├── register.el
├── registry.el
├── repeat.el
├── replace.el
├── reposition.el
├── reveal.el
├── rfn-eshadow.el
├── rot13.el
├── rtree.el
├── ruler-mode.el
├── savehist.el
├── saveplace.el
├── scroll-all.el
├── scroll-bar.el
├── scroll-lock.el
├── select.el
├── server.el
├── ses.el
├── shadowfile.el
├── shell.el
├── simple.el
├── skeleton.el              ; A very concise language extension for writing structured statement skeleton insertion commands for programming language modes.
├── so-long.el
├── sort.el
├── soundex.el
├── speedbar.el
├── sqlite.el
├── sqlite-mode.el
├── startup.el
├── strokes.el
├── subdirs.el
├── subr.el
├── svg.el
├── tab-bar.el
├── tabify.el
├── tab-line.el
├── talk.el
├── tar-mode.el
├── tempo.el
├── term.el
├── theme-loaddefs.el
├── thingatpt.el
├── thread.el
├── time.el
├── time-stamp.el
├── timezone.el
├── tmm.el
├── t-mouse.el
├── tool-bar.el
├── tooltip.el
├── touch-screen.el
├── transient.el
├── treesit.el
├── tree-widget.el
├── tutorial.el
├── type-break.el
├── uniquify.el
├── userlock.el
├── vcursor.el
├── version.el
├── view.el
├── visual-wrap.el
├── w32-fns.el
├── w32-vars.el
├── wdired.el
├── which-key.el
├── whitespace.el
├── wid-browse.el
├── wid-edit.el
├── widget.el
├── windmove.el
├── window.el
├── window-tool-bar.el  
├── winner.el
├── woman.el
├── xdg.el
├── x-dnd.el
├── xml.el
├── xt-mouse.el
├── xwidget.el
├── yank-media.el
```


## calc

```shell
├── calc-aent.el
├── calcalg2.el
├── calcalg3.el
├── calc-alg.el
├── calc-arith.el
├── calc-bin.el
├── calc-comb.el
├── calccomp.el
├── calc-cplx.el
├── calc.el                  ; Calc is split into many files.  This file is the main entry point. This file includes autoload commands for various other basic Calc facilities.
├── calc-embed.el
├── calc-ext.el              ; The more advanced features are based in calc-ext, which in turn contains autoloads for the rest of the Calc files.
├── calc-fin.el
├── calc-forms.el
├── calc-frac.el
├── calc-funcs.el
├── calc-graph.el
├── calc-help.el
├── calc-incom.el
├── calc-keypd.el
├── calc-lang.el
├── calc-loaddefs.el
├── calc-macs.el
├── calc-map.el
├── calc-math.el
├── calc-menu.el
├── calc-misc.el
├── calc-mode.el
├── calc-mtx.el
├── calc-nlfit.el
├── calc-poly.el
├── calc-prog.el
├── calc-rewr.el
├── calc-rules.el
├── calcsel2.el
├── calc-sel.el
├── calc-stat.el
├── calc-store.el
├── calc-stuff.el
├── calc-trail.el
├── calc-undo.el
├── calc-units.el
├── calc-vec.el
├── calc-yank.el
```