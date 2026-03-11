# Learning GNU Emacs

- 2026-03-11 first skimming

# 1 Emacs Basics/基础

## 1.1 Introducing Emacs!
## 1.2 Understanding Files and Buffers
## 1.3 A Word About Modes
## 1.4 Starting Emacs
## 1.5 About the Emacs Display
- The Toolbar
- The Menus
- The Mode Line
- The Minibuffer

![](https://www.scss.tcd.ie/Martin.Emms/2061/Useful/EmacsTutorial/emacs_display.gif)

## 1.6 Emacs 

- C-n
- M-n
- C-x something
- C-c something
- M-x long-command-name Enter


## 1.7 Opening a File `C-x C-f`
- If You Read the Wrong File: `C-x C-v`/`find-alternate-file`
- Letting Emacs Fill in the Blanks: `Tab`
- Inserting and Appending Files: `C-x i`
- How Emacs Chooses a Default Directory
## 1.8 Saving Files  `C-x C-s`
save as: `C-x C-w`

## 1.9 Leaving Emacs `C-x C-c`

## 1.10 Getting Help `C-h`

- `C-h ?`: a list of options
- `C-h f`: `describe-function`
- `C-h k`: `describe-key`
- `C-h t`: tutorial

the `*Help*` buffer

The Help Menu

# 2 Editing/编辑

## 2.1 Moving the Cursor
- Other Ways to Move the Cursor
- Moving a Screen (or More) at a Time
- Repeating Commands
- Centering the Display
- Emacs Commands and Your Keyboard
## 2.2 Deleting Text
- The Kill Ring
## 2.3 Marking Text to Delete, Move, or Copy
- Copying Text
- Recovering Earlier Deletions
- Selecting and Pasting
## 2.4 Emacs and the Clipboard
- Placing Text on the Clipboard
- Retrieving Text from the Clipboard
## 2.5 Editing Tricks and Shortcuts
- Fixing Transpositions
- Changing Capitalization
- Overwrite Mode
## 2.6 Canceling Commands and Undoing Changes
- Canceling Commands
- Undoing Changes
- Reverting a Buffer from a File
- Going Back to a Previous Version: Backup Files
- Recovering Lost Changes
## 2.7 Making Emacs Work the Way You Want
- Hiding the Toolbar
- Turning On CUA Mode for C-x, C-c, and C-v to Cut, Copy, and Paste
- Turning On Text Mode and Auto-Fill Mode Automatically
- Remapping Keys
- Problems You May Encounter

# 3 Search and Replace/搜索和替换

## 3.1 Different Kinds of Searches
- Incremental Search
- Simple Searches
- Word Search
## 3.2 Search and Replace/搜索和替换
- Simple Search and Replace Operations
- Query-Replace
- Repeating Query-Replaces (and Other Complex Commands)
- Recursive Editing
- Are Emacs Searches Case-Sensitive?
- Regular Expressions for Search and Replacement Operations
## 3.3 Checking Spelling Using Ispell
- Checking a Buffer
- Checking a Single Word
- Completing a Word
- Spellchecking on the Fly with Flyspell
## 3.4 Word Abbreviations/单词缩写
- Dynamic Abbreviations
- Word Abbreviation Mode
  - 1. Trying word abbreviations for one session
  - 2. Making word abbreviations part of your startup
  - 3. Deleting a word abbreviation
  - 4. Disabling word abbreviations
  - 5. Abbreviations and capitalization
- Problems You May Encounter

# 4 Using Buffers, Windows, and Frames/使用缓冲区, 窗口和框架

## 4.1 Understanding Buffers, Windows, and Frames
- Windows Versus Frames
- Buffers: Independent of Windows and Frames
- More About Buffers
## 4.2 Working with Multiple Buffers/缓冲区
- Switching Buffers
- Deleting Buffers
## 4.3 Working with Windows/窗口
- Creating Horizontal Windows
- Moving Between Windows
- Getting Rid of Windows
## 4.4 Working with Frames/框架
- Creating a New Frame
- Moving Between Frames
- Deleting and Minimizing Frames
## 4.5 More About Buffers
- Saving Multiple Buffers
- Renaming Buffers
- Read-Only Buffers
- Getting a List of Buffers
- Working with the Buffer List
## 4.6 More About Windows
- Creating Vertical or Side-by-Side Windows
- Navigating Windows
- Enlarging and Shrinking Windows
- Limits on Window Size
- Comparing Files Between Windows
## 4.7 Holding Your Place with Bookmarks/书签
- Setting Bookmarks
- Moving to a Bookmark
- Renaming and Deleting Bookmarks
- Working with a List of Bookmarks
- Annotating Bookmarks
- A Few More Bookmark Commands

# 5 Emacs as a Work Environment/Emacs作为工作环境

## 5.1 Executing Commands in Shell Buffers
- Running One Command at a Time: `M-!`
- Using Shell Mode
  - Which shell?
  - Making passwords invisible in shell mode
## 5.2 Using Dired, the Directory Editor/目录编辑器
- Viewing and Editing Files
- Deleting, Copying, and Renaming Files
- Compressing and Uncompressing Files
- Comparing Files
- Running Shell Commands on Files
- Working with Groups of Files
  - Selecting files
  - Selecting likely candidates for deletion
  - Selecting files by type
  - Using regular expressions to choose files
  - Operating on groups of files
- Navigating Directories
## 5.3 Printing from Emacs
## 5.4 Reading Manpages in Emacs
## 5.5 Using Time Management Tools
- Displaying the Calendar
  - Moving in the calendar
  - Displaying holidays
- Using the Diary
  - Creating a diary file
  - Adding diary entries
  - Displaying diary entries
- Problems You May Encounter

# 6 Writing Macros/键盘宏


In Emacs, a macro (keyboard macro) is a group of recorded keystrokes you can play back over and over again.

## 6.1 Defining a Macro
## 6.2 Tips for Creating Good Macros
## 6.3 A More Complicated Macro Example
## 6.4 Editing a Macro
## 6.5 The Macro Ring
## 6.6 Binding Your Macro to a Key
## 6.7 Naming, Saving, and Executing Your Macros
## 6.8 Building More Complicated Macros
- Pausing a Macro for Keyboard Input
  - Example
- Adding a Query to a Macro
  - Example
## 6.9 Executing Macros on a Region
## 6.10 Beyond Macros

# 7 Simple Text Formatting and Specialized Editing/简单文本格式化和特殊编辑

## 7.1 Using Tabs
- How Emacs 21 Handles Tabs by Default
- Changing Tab Stops
- What if You Want Literal Tabs?
- Changing Tab Width
- Tabs and Spaces
- Changing Tabs to Spaces (and Vice Versa)
## 7.2 Indenting Text
- Indenting Paragraphs
- Indenting the First Line of a Paragraph
- Filling Indented Paragraphs
  - Indenting regions
  - Other indentation tricks
- Changing Margins
- Using Fill Prefixes
## 7.3 Centering Text
## 7.4 Using Outline Mode
- Entering Outline Mode
- Hiding and Showing Text
- Editing While Text Is Hidden
- Marking Sections of the Outline
- Promoting and Demoting Sections
- Using Outline Minor Mode
## 7.5 Rectangle Editing
- CUA Rectangle Editing
## 7.6 Making Simple Drawings
- Drawing in Picture Mode
- Editing in Picture Mode
  - Cursor motion in picture mode
  - Inserting blank lines
- Drawing with the Mouse Using Artist
- Problems You May Encounter

# 8 Markup Language Support/标记语言支持

## 8.1 Comments
## 8.2 Font-Lock Mode
## 8.3 Writing HTML
- Using HTML Mode
  - Character encoding in HTML mode
    - Using ISO accents mode
    - Using the C-x 8 prefix
- Using HTML Helper Mode
  - 1. Starting HTML helper mode
  - 2. A brief tour of HTML helper mode
  - 3. Inserting an HTML template
  - 4. Putting tags around a region
  - 5. Using completion
  - 6. Turning on prompting
  - 7. Character encoding in HTML helper mode
## 8.4 Writing XML
- Writing XML with SGML Mode
- TEI Emacs: XML Authoring for Linux and Windows
- Writing XHTML Using nxml Mode
- Using psgml Mode
## 8.5 Marking up Text for TEX and LATEX
- Matching Braces
- Quotation Marks and Paragraphing
- Command Pairs
- Processing and Printing Text

# 9 Computer Language Support/计算机语言支持

## 9.1 Emacs as an IDE
- Compiling and Debugging
## 9.2 Writing Code
- Language Modes
  - Syntax
- Comments
- Indenting Code
- etags
- Fonts and Font-lock Mode
## 9.3 C and C++ Support
- Motion Commands
- Customizing Code Indentation Style
- Additional C and C++ Mode Features
- C++ Mode Differences
## 9.4 Java Support
- Java Mode
## 9.5 The Java Development Environment for Emacs (JDEE)
- Getting Started
- Installing CEDET
- Installing the ELisp Library
- Installing the JDEE
- Registering Your Java Tools
  - JDK tools.jar problems
- Editing with the JDEE
- Compiling and Running with the JDEE
- Debugging with the JDEE
- Learning More about the JDEE
## 9.6 Perl Support
- Perl Caveats
## 9.7 SQL Support
- Prerequisites
- Modes of Operation
  - Interactive mode
  - Editing mode
## 9.8 The Lisp Modes
- Indentation in Lisp Modes
- Comments in Lisp Modes
- Emacs Lisp Mode Differences
- Lisp Mode Differences
- Working with Lisp Fragments
  - Commands for evaluating a line of Lisp
  - Using Lisp interaction mode

# 10 Customizing Emacs

> Emacs has many settings which you can change. 
> 
> Most settings are customizable **variables**, which are also called user options. 
> There is a huge number of customizable variables, controlling numerous aspects of Emacs behavior; the variables documented in this manual are listed in Variable Index. 
> 
> A separate class of settings are the **faces**, which determine the fonts, colors, and other attributes of text (see Text Faces).

## 10.1 Using Custom/Custom交互接口
- Navigating Custom
- Common Options
- Customizing with Custom
- An Abbrev Mode Example
- The Options Menu/选项菜单
- A Dired Example
- But Where Is the Variable I Want?
## 10.2 Modifying the .emacs File Directly/直接修改.emacs文件
- Custom Versus .emacs
  - Will the real .emacs please stand up?
- Basic .emacs Statements
  - Caveat editor
- A Sample .emacs File
  - Editing .emacs
  - Saving .emacs
## 10.3 Modifying Fonts and Colors/修改字体和颜色
- Changing Fonts Interactively
- Automatic Highlighting and Coloring
  - Isearch
  - Buffer highlighting
- Customizing Fonts Through Custom
- Changing Colors
  - Changing the cursor color
- Saving Font- and Color-Enriched Text
  - Saving enriched text
## 10.4 Customizing Your Key Bindings/设置按键绑定
- Special Keys
- Unsetting Key Bindings
## 10.5 Setting Emacs Variables/设置Emacs变量
## 10.6 Finding Emacs Lisp Packages/查找Emacs的Lisp报
## 10.7 Starting Modes via Auto-Mode Customization/自动模式设置
## 10.8 Making Emacs Work the Way You Think It Should

# 11 Emacs Lisp Programming/Emacs Lisp编程

## 11.1 Introduction to Lisp
- Basic Lisp Entities
- Defining Functions
- Turning Lisp Functions into Emacs Commands
## 11.2 Lisp Primitive Functions
- Statement Blocks
- Control Structures
## 11.3 Useful Built-in Emacs Functions
- Buffers, Text, and Regions
- Regular Expressions
  - 1. Basic operators
  - 2. Grouping and alternation
  - 3. Context
  - 4. Retrieving portions of matches
  - 5. Regular expression operator summary
- A Treasure Trove of Examples
- Functions That Use Regular Expressions
- Finding Other Built-in Functions
## 11.4 Building an Automatic Template System
## 11.5 Programming a Major Mode
- Components of a Major Mode
- More Lisp Basics: Lists
- The Calculator Mode
- Lisp Code for the Calculator Mode

```lisp
;; Calculator mode.
;;
;; Supports the operators +, -, *, /, and % (remainder).
;; Commands:
;; c clear the stack
;; = print the value at the top of the stack
;; p print the entire stack contents
;;

(defvar calc-mode-map nil                          ; 模式代码中变量
  "Local keymap for calculator mode buffers.")

;; set up the calculator mode keymap with
;; C-j (linefeed) as "eval" key
(if calc-mode-map
    nil
  (setq calc-mode-map (make-sparse-keymap))        ; 少量的键绑定
  (define-key calc-mode-map "\C-j" 'calc-eval))

(defconst calc-number-regexp                       ; 模式代码中常量
  "-?\\([0-9]+\\.?\\|\\.\\)[0-9]*\\(e[0-9]+\\)?"
  "Regular expression for recognizing numbers.")
(defconst calc-operator-regexp "[-+*/%]"
  "Regular expression for recognizing operators.")
(defconst calc-command-regexp "[c=ps]"
  "Regular expression for recognizing commands.")
(defconst calc-whitespace "[ \t]"
  "Regular expression for recognizing whitespace.")

;; stack functions/栈函数
(defun calc-push (num)
  (if (numberp num)
      (setq calc-stack (cons num calc-stack))))
(defun calc-top ( )
  (if (not calc-stack)
      (error "stack empty.")
    (car calc-stack)))
(defun calc-pop ( )
  (let ((val (calc-top)))
    (if val
	(setq calc-stack (cdr calc-stack)))
    val))

;; functions for user commands/支持用户命令的函数
(defun calc-print-stack ( )
  "Print entire contents of stack, from top to bottom."
  (if calc-stack
      (progn
	(insert "\n")
	(let ((stk calc-stack))
	  (while calc-stack
	    (insert (number-to-string (calc-pop)) " "))
	  (setq calc-stack stk)))
    (error "stack empty.")))

(defun calc-clear-stack ( )
  "Clear the stack."
  (setq calc-stack nil)
  (message "stack cleared."))

(defun calc-command (tok)
  "Given a command token, perform the appropriate action."
  (cond ((equal tok "c")
	 (calc-clear-stack))
	((equal tok "=")
	 (insert "\n" (number-to-string (calc-top))))
	((equal tok "p")
	 (calc-print-stack))
	(t
	 (message (concat "invalid command: " tok)))))

(defun calc-operate (tok)
  "Given an arithmetic operator (as string), pop two numbers
off the stack, perform operation tok (given as string), push
the result onto the stack."
  (let ((op1 (calc-pop))
	(op2 (calc-pop)))
    (calc-push (funcall (read tok) op2 op1))))

(defun calc-push-number (tok)
  "Given a number (as string), push it (as number)
onto the stack."
  (calc-push (string-to-number tok)))

(defun calc-invalid-tok (tok)
  (error (concat "Invalid token: " tok)))

(defun calc-next-token ()
  "Pick up the next token, based on regexp search.
As side effects, advance point one past the token,
and set name of function to use to process the token."
  (let (tok)
    (cond ((looking-at calc-number-regexp)
	   (goto-char (match-end 0))
	   (setq calc-proc-fun 'calc-push-number))
	  ((looking-at calc-operator-regexp)
	   (forward-char 1)
	   (setq calc-proc-fun 'calc-operate))
	  ((looking-at calc-command-regexp)
	   (forward-char 1)
	   (setq calc-proc-fun 'calc-command))
	  ((looking-at ".")
	   (forward-char 1)
	   (setq calc-proc-fun 'calc-invalid-tok)))
    ;; pick up token and advance past it (and past whitespace)
    (setq tok (buffer-substring (match-beginning 0) (point)))
    (if (looking-at calc-whitespace)
	(goto-char (match-end 0)))
    tok))

(defun calc-eval ()
  "Main evaluation function for calculator mode.
Process all tokens on an input line."
  (interactive)
  (beginning-of-line)
  (while (not (eolp))
    (let ((tok (calc-next-token)))
      (funcall calc-proc-fun tok)))
  (insert "\n"))

(defun calc-mode ()
  "Calculator mode, using H-P style postfix notation.
Understands the arithmetic operators +, -, *, / and %,
plus the following commands:
c clear stack
= print top of stack
p print entire stack contents (top to bottom)
Linefeed (C-j) is bound to an evaluation function that
will evaluate everything on the current line. No
whitespace is necessary, except to separate numbers."
  (interactive)
  (pop-to-buffer "*Calc*" nil)           ; 模式使用的特殊缓冲区
  (kill-all-local-variables)
  (make-local-variable 'calc-stack)
  (setq calc-stack nil)
  (make-local-variable 'calc-proc-fun)
  (setq major-mode 'calc-mode)           ; 实现模式的函数符号
  (setq mode-name "Calculator")          ; 模式行中模式名称
  (use-local-map calc-mode-map)          ; 模式本地键映射
)
```

```
4 17*6-
p
62 
=
62
c
p
4 17*6
p
6 68
```

## 11.6 Customizing Existing Modes
## 11.7 Building Your Own Lisp Library
- Byte-Compiling Lisp Files

# 12 Version Control/版本控制

## 12.1 The Uses of Version Control
## 12.2 Version Control Concepts
## 12.3 How VC Helps with Basic Operations
## 12.4 Editing Comment Buffers
## 12.5 VC Command Summary
## 12.6 VC Mode Indicators
## 12.7 Which Version Control System?
## 12.8 Individual VC Commands
- Working with Groups and Subtrees of Files
- Difference Reports
- Retrieving Old Revisions
- Viewing Change Histories
- Registering a File
- Inserting Version Control Headers
- Making and Retrieving Snapshots
- Updating ChangeLog Files
- Renaming Version-Controlled Files
- When VC Gets Confused
## 12.9 Customizing VC
## 12.10 Extending VC
## 12.11 What VC Is Not
## 12.12 Using VC Effectively
## 12.13 Comparing with Ediff
- Starting Ediff
- Using Ediff
- Making Changes
- Quitting Ediff
- Recovering from Confusion
- Learning More
- Customizing Ediff
- Invoking Ediff Automatically

# 13 Platform-Specific Considerations/平台特定考虑

## 13.1 Emacs and Unix
- Where to Get Emacs?
  - Downloading Emacs from the Web
- Where to Put Emacs?
- Uncompressing and Unpacking
- Downloading Emacs from CVS
- Building Emacs
## 13.2 Emacs and Mac OS X
- "But I Already Have Emacs"
- Installing Prebuilt Emacs on Mac OS X
  - Downloading Alex Rice's application bundle of Emacs 21.3.5
- Building Emacs from Source on Mac OS X
  - Before you build
    - Jaguar (Mac OS X 10.2) preparation
- Starting Emacs from the Command Line on Mac OS X
- Mac OS X and the Meta Key
- Installing Ispell
## 13.3 Emacs and Windows
- Installing Emacs
  - Installing the latest binaries: Nqmacs
  - Installing Emacs from the FSF
- Where to Put Your .emacs File
- Starting Emacs from the Command Line
- Making Emacs Act like Windows: CUA Mode
- Installing Ispell

# 14 The Help System/帮助系统

## 14.1 Using the Tutorial
## 14.2 Help Commands
- Detail Information

`C-h C-h`/`C-h ?`
```
(Type <PageDown> or <PageUp> to scroll, C-s to search, or q to exit.)

Commands, Keys and Functions

   m 	Show help for current major and minor modes and their commands
   b 	Show all key bindings
   k 	Show help for key
   c 	Show help for key briefly
   w 	Show which key runs a specific command

   a 	Search for commands (see also M-x apropos)
   d 	Search documentation of functions, variables, and other items
   x 	Show help for command
   f 	Show help for function
   4 s 	Show the source for what’s being described in *Help*
   v 	Show help for variable
   o 	Show help for function or variable

Manuals

   r 	Show Emacs manual
   F 	Show Emacs manual section for command
   K 	Show Emacs manual section for a key sequence
   i 	Show all installed manuals
   R 	Show a specific manual
   S 	Show description of symbol in pertinent manual

Other Help Commands

   C-e 	Extending Emacs with external packages
   p 	Search for Emacs packages (see also M-x list-packages)
   P 	Describe a specific Emacs package

   t 	Start the Emacs tutorial
   C-q 	Display the quick help buffer.
   e 	Show recent messages (from echo area)
   l 	Show last 300 input keystrokes (lossage)
   . 	Show local help at point

Miscellaneous

   C-a 	About Emacs
   C-f 	Emacs FAQ
   C-n 	News of recent changes
   C-p 	Known problems
   C-d 	Debugging Emacs

   g 	About the GNU project
   C-c 	Emacs copying permission (GNU General Public License)
   C-o 	Emacs ordering and distribution information
   C-m 	Order printed manuals
   C-t 	Emacs TODO
   C-w 	Information on absence of warranty

Internationalization and Coding Systems

   I 	Describe input method
   C 	Describe coding system
   L 	Describe language environment
   s 	Show current syntax table
   h 	Display the HELLO file illustrating various scripts
```

- Apropos Commands
```
Help >
  Search Documentation >
    Find Commands by Name: apropos-command
    Find Options by Name: apropos-variable
    Find Options by Value: apropos-value
    Search Documentation Strings: apropos-documentation
    Find Any Object by Name: apropos
```

## 14.3 Help with Complex Emacs Commands
## 14.4 Navigating Emacs Documentation
- Using Info to Read Manuals
- FAQ, News, and Antinews
## 14.5 Completion
- Customizing Completion

# A. Emacs Variables/Emacs变量

# B. Emacs Lisp Packages/Emacs Lisp包

# C. Bugs and Bug Fixes
# D. Online Resources
# E. Quick Reference