# GNU Emacs Manual
* https://www.gnu.org/software/emacs/manual/html_mono/emacs.html

2026-02 30.2

# 1 The Organization of the Screen
## 1.1 Point
## 1.2 The Echo Area
## 1.3 The Mode Line
## 1.4 The Menu Bar
# 2 Kinds of User Input
# 3 Keys
# 4 Mouse Input
# 5 Keys and Commands
# 6 Touchscreen Input and Virtual Keyboards
## 6.1 Using Emacs on Touchscreens
## 6.2 Using Emacs with Virtual Keyboards
# 7 Entering Emacs
# 8 Exiting Emacs
# 9 Basic Editing Commands
## 9.1 Inserting Text
## 9.2 Changing the Location of Point
## 9.3 Erasing Text
## 9.4 Undoing Changes
## 9.5 Files
## 9.6 Help
## 9.7 Blank Lines
## 9.8 Continuation Lines
## 9.9 Cursor Position Information
## 9.10 Numeric Arguments
## 9.11 Repeating a Command
# 10 The Minibuffer
## 10.1 Using the Minibuffer
## 10.2 Minibuffers for File Names
## 10.3 Editing in the Minibuffer
## 10.4 Completion
- 10.4.1 Completion Example
- 10.4.2 Completion Commands
- 10.4.3 Completion Exit
- 10.4.4 How Completion Alternatives Are Chosen
- 10.4.5 Completion Options
## 10.5 Minibuffer History
## 10.6 Repeating Minibuffer Commands
## 10.7 Entering passwords
## 10.8 Yes or No Prompts
# 11 Running Commands by Name
# 12 Help
## 12.1 Help Summary
## 12.2 Documentation for a Key
## 12.3 Help by Command or Variable Name
## 12.4 Apropos
## 12.5 Help Mode Commands
## 12.6 Keyword Search for Packages
## 12.7 Help for International Language Support
## 12.8 Other Help Commands
## 12.9 Help Files
## 12.10 Help on Active Text and Tooltips
# 13 The Mark and the Region
## 13.1 Setting the Mark
## 13.2 Commands to Mark Textual Objects
## 13.3 Operating on the Region
## 13.4 The Mark Ring
## 13.5 The Global Mark Ring
## 13.6 Shift Selection
## 13.7 Disabling Transient Mark Mode
# 14 Killing and Moving Text
## 14.1 Deletion and Killing
- 14.1.1 Deletion
- 14.1.2 Killing by Lines
- 14.1.3 Other Kill Commands
- 14.1.4 Options for Killing
## 14.2 Yanking
- 14.2.1 The Kill Ring
- 14.2.2 Yanking Earlier Kills
- 14.2.3 Appending Kills
## 14.3 “Cut and Paste” Operations on Graphical Displays
- 14.3.1 Using the Clipboard
- 14.3.2 Cut and Paste with Other Window Applications
- 14.3.3 Secondary Selection
## 14.4 Accumulating Text
## 14.5 Rectangles
## 14.6 CUA Bindings
# 15 Registers
## 15.1 Saving Positions in Registers
## 15.2 Saving Text in Registers
## 15.3 Saving Rectangles in Registers
## 15.4 Saving Window and Frame Configurations in Registers
## 15.5 Keeping Numbers in Registers
## 15.6 Keeping File and Buffer Names in Registers
## 15.7 Keyboard Macro Registers
## 15.8 Bookmarks

# 16 Controlling the Display/控制显示

Emacs can display text in several different styles, called **faces/风格**. 
Each face can specify various face attributes, such as the font/字体, height, weight, slant, foreground and background color/颜色, and underlining or overlining. 
Most major modes assign faces to the text automatically, via Font Lock *mode*.

## 16.1 Scrolling
## 16.2 Recentering
## 16.3 Automatic Scrolling
## 16.4 Horizontal Scrolling
## 16.5 Narrowing
## 16.6 View Mode
## 16.7 Follow Mode
## 16.8 Text Faces/
## 16.9 Colors for Faces
- 16.9.1 Color Names
- 16.9.2 RGB Triplets
## 16.10 Standard Faces
## 16.11 Icons
## 16.12 Text Scale
## 16.13 Font Lock mode
- 16.13.1 Traditional Font Lock
- 16.13.2 Parser-based Font Lock
## 16.14 Interactive Highlighting
## 16.15 Window Fringes
## 16.16 Displaying Boundaries
## 16.17 Useless Whitespace
## 16.18 Selective Display
## 16.19 Optional Mode Line Features
## 16.20 How Text Is Displayed
## 16.21 Displaying the Cursor
## 16.22 Line Truncation
## 16.23 Visual Line Mode
## 16.24 Customization of Display

# 17 Searching and Replacement
## 17.1 Incremental Search
- 17.1.1 Basics of Incremental Search
- 17.1.2 Repeating Incremental Search
- 17.1.3 Isearch Yanking
- 17.1.4 Errors in Incremental Search
- 17.1.5 Special Input for Incremental Search
- 17.1.6 Not Exiting Incremental Search
- 17.1.7 Searching the Minibuffer
## 17.2 Nonincremental Search
## 17.3 Word Search
## 17.4 Symbol Search
## 17.5 Regular Expression Search
## 17.6 Syntax of Regular Expressions
## 17.7 Backslash in Regular Expressions
## 17.8 Regular Expression Example
## 17.9 Lax Matching During Searching
## 17.10 Replacement Commands
- 17.10.1 Unconditional Replacement
- 17.10.2 Regexp Replacement
- 17.10.3 Replace Commands and Lax Matches
- 17.10.4 Query Replace
## 17.11 Other Search-and-Loop Commands
## 17.12 Tailoring Search to Your Needs
# 18 Commands for Fixing Typos
## 18.1 Undo
## 18.2 Transposing Text
## 18.3 Case Conversion
## 18.4 Checking and Correcting Spelling
# 19 Keyboard Macros
## 19.1 Basic Use
## 19.2 The Keyboard Macro Ring
## 19.3 The Keyboard Macro Counter
## 19.4 Executing Macros with Variations
## 19.5 Naming and Saving Keyboard Macros
## 19.6 Editing a Keyboard Macro
## 19.7 Stepwise Editing a Keyboard Macro
## 19.8 Listing and Editing Keyboard Macros
# 20 File Handling
## 20.1 File Names
## 20.2 Visiting Files
## 20.3 Saving Files
- 20.3.1 Commands for Saving Files
- 20.3.2 Backup Files
- 20.3.2.1 Single or Numbered Backups
- 20.3.2.2 Automatic Deletion of Backups
- 20.3.2.3 Copying vs. Renaming
- 20.3.3 Customizing Saving of Files
- 20.3.4 Protection against Simultaneous Editing
- 20.3.5 Shadowing Files
- 20.3.6 Updating Time Stamps Automatically
- 20.3.6.1 Customizing the Time Stamp
- 20.3.6.2 Forcing Time Stamps for One File
## 20.4 Reverting a Buffer
## 20.5 Auto Revert: Keeping buffers automatically up-to-date
- 20.5.1 Auto Reverting Non-File Buffers
- 20.5.1.1 Auto Reverting the Buffer Menu
- 20.5.1.2 Auto Reverting Dired buffers
## 20.6 Auto-Saving: Protection Against Disasters
- 20.6.1 Auto-Save Files
- 20.6.2 Controlling Auto-Saving
- 20.6.3 Recovering Data from Auto-Saves
## 20.7 File Name Aliases
## 20.8 File Directories
## 20.9 Comparing Files
## 20.10 Diff Mode
## 20.11 Copying, Naming and Renaming Files
## 20.12 Miscellaneous File Operations
## 20.13 Accessing Compressed Files
## 20.14 File Archives
## 20.15 Remote Files
## 20.16 Quoted File Names
## 20.17 File Name Cache
## 20.18 Convenience Features for Finding Files
## 20.19 Viewing Image Files
## 20.20 Filesets
# 21 Using Multiple Buffers
## 21.1 Creating and Selecting Buffers
## 21.2 Listing Existing Buffers
## 21.3 Miscellaneous Buffer Operations
## 21.4 Killing Buffers
## 21.5 Operating on Several Buffers
## 21.6 Indirect Buffers
## 21.7 Convenience Features and Customization of Buffer Handling
- 21.7.1 Making Buffer Names Unique
- 21.7.2 Fast minibuffer selection
- 21.7.3 Customizing Buffer Menus
# 22 Multiple Windows
## 22.1 Concepts of Emacs Windows
## 22.2 Splitting Windows
## 22.3 Using Other Windows
## 22.4 Displaying in Another Window
## 22.5 Deleting and Resizing Windows
## 22.6 Displaying a Buffer in a Window
- 22.6.1 How display-buffer works
- 22.6.2 Displaying non-editable buffers.
## 22.7 Convenience Features for Window Handling
## 22.8 Window Tab Line
## 22.9 Window Tool Bar
# 23 Frames and Graphical Displays
## 23.1 Mouse Commands for Editing
## 23.2 Mouse Commands for Words and Lines
## 23.3 Following References with the Mouse
## 23.4 Mouse Clicks for Menus
## 23.5 Mode Line Mouse Commands
## 23.6 Creating Frames
## 23.7 Frame Commands
## 23.8 Fonts
## 23.9 Speedbar Frames
## 23.10 Multiple Displays
## 23.11 Frame Parameters
## 23.12 Scroll Bars
## 23.13 Window Dividers
## 23.14 Drag and Drop
## 23.15 Menu Bars
## 23.16 Tool Bars
## 23.17 Tab Bars
## 23.18 Using Dialog Boxes
## 23.19 Tooltips
## 23.20 Mouse Avoidance
## 23.21 Text Terminals
## 23.22 Using a Mouse in Text Terminals
# 24 International Character Set Support
## 24.1 Introduction to International Character Sets
## 24.2 Language Environments
## 24.3 Input Methods
## 24.4 Selecting an Input Method
## 24.5 Coding Systems
## 24.6 Recognizing Coding Systems
## 24.7 Specifying a File’s Coding System
## 24.8 Choosing Coding Systems for Output
## 24.9 Specifying a Coding System for File Text
## 24.10 Coding Systems for Interprocess Communication
## 24.11 Coding Systems for File Names
## 24.12 Coding Systems for X Keyboard Input
## 24.13 Coding Systems for Terminal I/O
## 24.14 Fontsets
## 24.15 Defining Fontsets
## 24.16 Modifying Fontsets
## 24.17 Undisplayable Characters
## 24.18 Unibyte Editing Mode
## 24.19 Charsets
## 24.20 Bidirectional Editing
# 25 Major and Minor Modes
## 25.1 Major Modes
## 25.2 Minor Modes
## 25.3 Choosing File Modes
# 26 Indentation
## 26.1 Indentation Commands
## 26.2 Tab Stops
## 26.3 Tabs vs. Spaces
## 26.4 Convenience Features for Indentation
## 26.5 Code Alignment
# 27 Commands for Human Languages
## 27.1 Words
## 27.2 Sentences
## 27.3 Paragraphs
## 27.4 Pages
## 27.5 Quotation Marks
## 27.6 Filling Text
- 27.6.1 Auto Fill Mode
- 27.6.2 Explicit Fill Commands
- 27.6.3 The Fill Prefix
- 27.6.4 Adaptive Filling
## 27.7 Case Conversion Commands
## 27.8 Text Mode
## 27.9 Outline Mode
- 27.9.1 Outline Minor Mode
- 27.9.2 Format of Outlines
- 27.9.3 Outline Motion Commands
- 27.9.4 Outline Visibility Commands
- 27.9.5 Viewing One Outline in Multiple Views
- 27.9.6 Folding Editing
## 27.10 Org Mode
- 27.10.1 Org as an organizer
- 27.10.2 Org as an authoring system
## 27.11 TeX Mode
- 27.11.1 TeX Editing Commands
- 27.11.2 LaTeX Editing Commands
- 27.11.3 TeX Printing Commands
- 27.11.4 TeX Mode Miscellany
## 27.12 SGML and HTML Modes
## 27.13 Nroff Mode
## 27.14 Enriched Text
- 27.14.1 Enriched Mode
- 27.14.2 Hard and Soft Newlines
- 27.14.3 Editing Format Information
- 27.14.4 Faces in Enriched Text
- 27.14.5 Indentation in Enriched Text
- 27.14.6 Justification in Enriched Text
- 27.14.7 Setting Other Text Properties
## 27.15 Editing Text-based Tables
- 27.15.1 What is a Text-based Table?
- 27.15.2 Creating a Table
- 27.15.3 Table Recognition
- 27.15.4 Commands for Table Cells
- 27.15.5 Cell Justification
- 27.15.6 Table Rows and Columns
- 27.15.7 Converting Between Plain Text and Tables
- 27.15.8 Table Miscellany
## 27.16 Two-Column Editing
# 28 Editing Programs
## 28.1 Major Modes for Programming Languages
## 28.2 Top-Level Definitions, or Defuns
- 28.2.1 Left Margin Convention
- 28.2.2 Moving by Defuns
- 28.2.3 Moving by Sentences
- 28.2.4 Imenu
- 28.2.5 Which Function Mode
## 28.3 Indentation for Programs
- 28.3.1 Basic Program Indentation Commands
- 28.3.2 Indenting Several Lines
- 28.3.3 Customizing Lisp Indentation
- 28.3.4 Commands for C Indentation
- 28.3.5 Customizing C Indentation
## 28.4 Commands for Editing with Parentheses
- 28.4.1 Expressions with Balanced Parentheses
- 28.4.2 Moving in the Parenthesis Structure
- 28.4.3 Matching Parentheses
## 28.5 Manipulating Comments
- 28.5.1 Comment Commands
- 28.5.2 Multiple Lines of Comments
- 28.5.3 Options Controlling Comments
## 28.6 Documentation Lookup
- 28.6.1 Info Documentation Lookup
- 28.6.2 Man Page Lookup
- 28.6.3 Programming Language Documentation Lookup
## 28.7 Hideshow minor mode
## 28.8 Completion for Symbol Names
## 28.9 MixedCase Words
## 28.10 Semantic
## 28.11 Other Features Useful for Editing Programs
## 28.12 C and Related Modes
- 28.12.1 C Mode Motion Commands
- 28.12.2 Electric C Characters
- 28.12.3 Hungry Delete Feature in C
- 28.12.4 Other Commands for C Mode
## 28.13 Asm Mode
## 28.14 Fortran Mode
- 28.14.1 Motion Commands
- 28.14.2 Fortran Indentation
- 28.14.2.1 Fortran Indentation and Filling Commands
- 28.14.2.2 Continuation Lines
- 28.14.2.3 Line Numbers
- 28.14.2.4 Syntactic Conventions
- 28.14.2.5 Variables for Fortran Indentation
- 28.14.3 Fortran Comments
- 28.14.4 Auto Fill in Fortran Mode
- 28.14.5 Checking Columns in Fortran
- 28.14.6 Fortran Keyword Abbrevs
# 29 Compiling and Testing Programs
## 29.1 Running Compilations under Emacs
## 29.2 Compilation Mode
## 29.3 Subshells for Compilation
## 29.4 Searching with Grep under Emacs
## 29.5 Finding Syntax Errors On The Fly
## 29.6 Running Debuggers Under Emacs
- 29.6.1 Starting GUD
- 29.6.2 Debugger Operation
- 29.6.3 Commands of GUD
- 29.6.4 GUD Customization
- 29.6.5 GDB Graphical Interface
- 29.6.5.1 GDB User Interface Layout
- 29.6.5.2 Source Buffers
- 29.6.5.3 Breakpoints Buffer
- 29.6.5.4 Threads Buffer
- 29.6.5.5 Stack Buffer
- 29.6.5.6 Other GDB Buffers
- 29.6.5.7 Watch Expressions
- 29.6.5.8 Multithreaded Debugging
## 29.7 Executing Lisp Expressions
## 29.8 Libraries of Lisp Code for Emacs
## 29.9 Evaluating Emacs Lisp Expressions
## 29.10 Lisp Interaction Buffers
## 29.11 Running an External Lisp
# 30 Maintaining Large Programs
## 30.1 Version Control
- 30.1.1 Introduction to Version Control
- 30.1.1.1 Understanding the Problems it Addresses
- 30.1.1.2 Supported Version Control Systems
- 30.1.1.3 Concepts of Version Control
- 30.1.1.4 Merge-based vs Lock-based Version Control
- 30.1.1.5 Changeset-based vs File-based Version Control
- 30.1.1.6 Decentralized vs Centralized Repositories
- 30.1.1.7 Types of Log File
- 30.1.2 Version Control and the Mode Line
- 30.1.3 Basic Editing under Version Control
- 30.1.3.1 Basic Version Control with Merging
- 30.1.3.2 Basic Version Control with Locking
- 30.1.3.3 Advanced Control in C-x v v
- 30.1.4 Features of the Log Entry Buffer
- 30.1.5 Registering a File for Version Control
- 30.1.6 Examining And Comparing Old Revisions
- 30.1.7 VC Change Log
- 30.1.8 Undoing Version Control Actions
- 30.1.9 Ignore Version Control Files
- 30.1.10 VC Directory Mode
- 30.1.10.1 The VC Directory Buffer
- 30.1.10.2 VC Directory Commands
- 30.1.11 Version Control Branches
- 30.1.11.1 Switching between Branches
- 30.1.11.2 Pulling/Pushing Changes into/from a Branch
- 30.1.11.3 Merging Branches
- 30.1.11.4 Creating New Branches
- 30.1.12 Miscellaneous Commands and Features of VC
- 30.1.12.1 Change Logs and VC
- 30.1.12.2 Deleting and Renaming Version-Controlled Files
- 30.1.12.3 Revision Tags
- 30.1.12.4 Inserting Version Control Headers
- 30.1.12.5 Editing VC Commands
- 30.1.12.6 Preparing Patches
- 30.1.13 Customizing VC
- 30.1.13.1 General Options
- 30.1.13.2 Options for RCS and SCCS
- 30.1.13.3 Options specific for CVS
## 30.2 Working with Projects
- 30.2.1 Project Commands That Operate on Files
- 30.2.2 Project Commands That Operate on Buffers
- 30.2.3 Switching Projects
- 30.2.4 Managing the Project List File
## 30.3 Change Logs
- 30.3.1 Change Log Commands
- 30.3.2 Format of ChangeLog
## 30.4 Find Identifier References
- 30.4.1 Find Identifiers
- 30.4.1.1 Looking Up Identifiers
- 30.4.1.2 Commands Available in the *xref* Buffer
- 30.4.1.3 Searching and Replacing with Identifiers
- 30.4.1.4 Identifier Inquiries
- 30.4.2 Tags Tables
- 30.4.2.1 Source File Tag Syntax
- 30.4.2.2 Creating Tags Tables
- 30.4.2.3 Etags Regexps
- 30.4.3 Selecting a Tags Table
## 30.5 Emacs Development Environment
## 30.6 Merging Files with Emerge
- 30.6.1 Overview of Emerge
- 30.6.2 Submodes of Emerge
- 30.6.3 State of a Difference
- 30.6.4 Merge Commands
- 30.6.5 Exiting Emerge
- 30.6.6 Combining the Two Versions
- 30.6.7 Fine Points of Emerge
## 30.7 Bug Reference
# 31 Abbrevs
## 31.1 Abbrev Concepts
## 31.2 Defining Abbrevs
## 31.3 Controlling Abbrev Expansion
## 31.4 Abbrevs Suggestions
## 31.5 Examining and Editing Abbrevs
## 31.6 Saving Abbrevs
## 31.7 Dynamic Abbrev Expansion
## 31.8 Customizing Dynamic Abbreviation
# 32 Dired, the Directory Editor
## 32.1 Entering Dired
## 32.2 Navigation in the Dired Buffer
## 32.3 Deleting Files with Dired
## 32.4 Flagging Many Files at Once
## 32.5 Visiting Files in Dired
## 32.6 Dired Marks vs. Flags
## 32.7 Operating on Files
## 32.8 Shell Commands in Dired
## 32.9 Shell Command Guessing
## 32.10 Transforming File Names in Dired
## 32.11 File Comparison with Dired
## 32.12 Subdirectories in Dired
## 32.13 Subdirectory Switches in Dired
## 32.14 Moving Over Subdirectories
## 32.15 Hiding Subdirectories
## 32.16 Updating the Dired Buffer
## 32.17 Dired and find
## 32.18 Editing the Dired Buffer
## 32.19 Viewing Image Thumbnails in Dired
## 32.20 Other Dired Features
# 33 The Calendar and the Diary
## 33.1 Movement in the Calendar
- 33.1.1 Motion by Standard Lengths of Time
- 33.1.2 Beginning or End of Week, Month or Year
- 33.1.3 Specified Dates
## 33.2 Scrolling in the Calendar
## 33.3 Counting Days
## 33.4 Miscellaneous Calendar Commands
## 33.5 Writing Calendar Files
## 33.6 Holidays
## 33.7 Times of Sunrise and Sunset
## 33.8 Phases of the Moon
## 33.9 Conversion To and From Other Calendars
- 33.9.1 Supported Calendar Systems
- 33.9.2 Converting To Other Calendars
- 33.9.3 Converting From Other Calendars
## 33.10 The Diary
- 33.10.1 The Diary File
- 33.10.2 Displaying the Diary
- 33.10.3 Date Formats
- 33.10.4 Commands to Add to the Diary
- 33.10.5 Special Diary Entries
- 33.10.6 Appointments
- 33.10.7 Importing and Exporting Diary Entries
## 33.11 Daylight Saving Time
## 33.12 Summing Time Intervals
## 33.13 More advanced features of the Calendar and Diary
- 33.13.1 Customizing the Calendar
- 33.13.2 Customizing the Holidays
- 33.13.3 Converting from the Mayan Calendar
- 33.13.4 Date Display Format
- 33.13.5 Time Display Format
- 33.13.6 Customizing the Diary
- 33.13.7 Diary Entries Using non-Gregorian Calendars
- 33.13.8 Diary Display
- 33.13.9 Fancy Diary Display
- 33.13.10 Sexp Entries and the Fancy Diary Display
# 34 Sending Mail
## 34.1 The Format of the Mail Buffer
## 34.2 Mail Header Fields
## 34.3 Mail Aliases
## 34.4 Mail Commands
- 34.4.1 Mail Sending
- 34.4.2 Mail Header Editing
- 34.4.3 Citing Mail
- 34.4.4 Mail Miscellany
## 34.5 Mail Signature
## 34.6 Mail Amusements
## 34.7 Mail-Composition Methods
# 35 Reading Mail with Rmail
## 35.1 Basic Concepts of Rmail
## 35.2 Scrolling Within a Message
## 35.3 Moving Among Messages
## 35.4 Deleting Messages
## 35.5 Rmail Files and Inboxes
## 35.6 Multiple Rmail Files
## 35.7 Copying Messages Out to Files
## 35.8 Labels
## 35.9 Rmail Attributes
## 35.10 Sending Replies
## 35.11 Summaries
- 35.11.1 Making Summaries
- 35.11.2 Editing in Summaries
## 35.12 Sorting the Rmail File
## 35.13 Display of Messages
## 35.14 Rmail and Coding Systems
## 35.15 Editing Within a Message
## 35.16 Digest Messages
## 35.17 Reading Rot13 Messages
## 35.18 movemail program
## 35.19 Retrieving Mail from Remote Mailboxes
## 35.20 Retrieving Mail from Local Mailboxes in Various Formats
# 36 Email and Usenet News with Gnus
## 36.1 Gnus Buffers
## 36.2 When Gnus Starts Up
## 36.3 Using the Gnus Group Buffer
## 36.4 Using the Gnus Summary Buffer
# 37 Host Security
# 38 Network Security
# 39 Document Viewing
## 39.1 DocView Navigation
## 39.2 DocView Searching
## 39.3 DocView Slicing
## 39.4 DocView Conversion
# 40 Running Shell Commands from Emacs
## 40.1 Single Shell Commands
## 40.2 Interactive Subshell
## 40.3 Shell Mode
## 40.4 Shell Prompts
## 40.5 Shell Command History
- 40.5.1 Shell History Ring
- 40.5.2 Shell History Copying
- 40.5.3 Shell History References
## 40.6 Directory Tracking
## 40.7 Shell Mode Options
## 40.8 Emacs Terminal Emulator
## 40.9 Term Mode
## 40.10 Remote Host Shell
## 40.11 Serial Terminal
# 41 Using Emacs as a Server
## 41.1 TCP Emacs server
## 41.2 Invoking emacsclient
## 41.3 emacsclient Options
# 42 Printing Hard Copies
## 42.1 PostScript Hardcopy
## 42.2 Variables for PostScript Hardcopy
## 42.3 Printing Package
# 43 Sorting Text
# 44 Editing Pictures
## 44.1 Basic Editing in Picture Mode
## 44.2 Controlling Motion after Insert
## 44.3 Picture Mode Tabs
## 44.4 Picture Mode Rectangle Commands
# 45 Editing Binary Files
# 46 Saving Emacs Sessions
# 47 Recursive Editing Levels
# 48 Hyperlinking and Web Navigation Features
## 48.1 Web Browsing with EWW
## 48.2 Embedded WebKit Widgets
## 48.3 Following URLs
## 48.4 Activating URLs
## 48.5 Finding Files and URLs at Point
# 49 Games and Other Amusements
# 50 Emacs Lisp Packages
## 50.1 The Package Menu Buffer
## 50.2 Package Statuses
## 50.3 Package Installation
## 50.4 Package Files and Directory Layout
## 50.5 Fetching Package Sources
- 50.5.1 Specifying Package Sources

# 51 Customization/设置
## 51.1 Easy Customization Interface
- 51.1.1 Customization Groups
- 51.1.2 Browsing and Searching for Settings
- 51.1.3 Changing a Variable
- 51.1.4 Saving Customizations
- 51.1.5 Customizing Faces
- 51.1.6 Customizing Specific Items
- 51.1.7 Custom Themes
- 51.1.8 Creating Custom Themes
## 51.2 Variables
- 51.2.1 Examining and Setting Variables
- 51.2.2 Hooks
- 51.2.3 Local Variables
- 51.2.4 Local Variables in Files
- 51.2.4.1 Specifying File Variables
- 51.2.4.2 Safety of File Variables
- 51.2.5 Per-Directory Local Variables
- 51.2.5.1 Per-Directory Variables via EditorConfig
- 51.2.6 Per-Connection Local Variables
## 51.3 Customizing Key Bindings
- 51.3.1 Keymaps
- 51.3.2 Prefix Keymaps
- 51.3.3 Local Keymaps
- 51.3.4 Minibuffer Keymaps
- 51.3.5 Changing Key Bindings Interactively
- 51.3.6 Rebinding Keys in Your Init File
- 51.3.7 Modifier Keys
- 51.3.8 Rebinding Function Keys
- 51.3.9 Named ASCII Control Characters
- 51.3.10 Rebinding Mouse Buttons
- 51.3.11 Disabling Commands
## 51.4 The Emacs Initialization File
- 51.4.1 Init File Syntax
- 51.4.2 Init File Examples
- 51.4.3 Terminal-specific Initialization
- 51.4.4 How Emacs Finds Your Init File
- 51.4.5 Non-ASCII Characters in Init Files
- 51.4.6 The Early Init File
## 51.5 Keeping Persistent Authentication Information

# 52 Quitting and Aborting

# 53 Dealing with Emacs Trouble
## 53.1 Recursive Editing Levels
## 53.2 Garbage on the Screen
## 53.3 Garbage in the Text
## 53.4 Running out of Memory
## 53.5 When Emacs Crashes
## 53.6 Recovery After a Crash
## 53.7 Emergency Escape
## 53.8 If DEL Fails to Delete

# 54 Reporting Bugs
## 54.1 Reading Existing Bug Reports and Known Problems
## 54.2 When Is There a Bug
## 54.3 Understanding Bug Reporting
## 54.4 Checklist for Bug Reports
## 54.5 Sending Patches for GNU Emacs
# 55 Contributing to Emacs Development

## 55.1 Coding Standards
## 55.2 Copyright Assignment

# 56 How To Get Help with GNU Emacs

# Appendix A GNU GENERAL PUBLIC LICENSE

# Appendix B GNU Free Documentation License

# Appendix C Command Line Arguments for Emacs Invocation
## C.1 Action Arguments
## C.2 Initial Options
## C.3 Command Argument Example
## C.4 Environment Variables
## C.4.1 General Variables
## C.4.2 Miscellaneous Variables
## C.4.3 The MS-Windows System Registry
## C.5 Specifying the Display Name
## C.6 Font Specification Options
## C.7 Window Color Options
## C.8 Options for Window Size and Position
## C.9 Internal and Outer Borders
## C.10 Frame Titles
## C.11 Icons
## C.12 Other Display Options

# Appendix D X Options and Resources
## D.1 X Resources
## D.2 Table of X Resources for Emacs
## D.3 Lucid Menu And Dialog X Resources
## D.4 Motif Menu X Resources
## D.5 GTK+ resources
## D.5.1 GTK+ Resource Basics
## D.5.2 GTK+ widget names
## D.5.3 GTK+ Widget Names in Emacs
## D.5.4 GTK+ styles

# Appendix E Emacs 29 Antinews

# Appendix F Emacs and macOS / GNUstep
## F.1 Basic Emacs usage under macOS and GNUstep
## F.1.1 Grabbing environment variables
## F.2 Mac / GNUstep Customization
## F.2.1 Modifier keys
## F.2.2 Frame Variables
## F.2.3 macOS Trackpad/Mousewheel Variables
## F.3 Windowing System Events under macOS / GNUstep
## F.4 GNUstep Support

# Appendix G Emacs and Haiku
## G.1 Haiku Installation and Startup
## G.2 Font Backends and Selection under Haiku

# Appendix H Emacs and Android
## H.1 Android History
## H.2 Starting Emacs on Android
## H.3 What Files Emacs Can Access on Android
## H.4 Accessing Files from Other Programs on Android
## H.5 Running Emacs under Android
## H.6 The Android Window System
## H.7 Font Backends and Selection under Android
## H.8 Troubleshooting Startup Problems on Android
## H.9 Installing Extra Software on Android

# Appendix I Emacs and Microsoft Windows/MS-DOS
## I.1 How to Start Emacs on MS-Windows
## I.2 Text Files and Binary Files
## I.3 File Names on MS-Windows
## I.4 Emulation of ls on MS-Windows
## I.5 HOME and Startup Directories on MS-Windows
## I.6 Keyboard Usage on MS-Windows
## I.7 Mouse Usage on MS-Windows
## I.8 Subprocesses on Windows 9X/ME and Windows NT/2K/XP/Vista/7/8/10
## I.9 Printing and MS-Windows
## I.10 Specifying Fonts on MS-Windows
## I.11 Miscellaneous Windows-specific features
## I.12 Emacs and MS-DOS
## I.12.1 Keyboard Usage on MS-DOS
## I.12.2 Mouse Usage on MS-DOS
## I.12.3 Display on MS-DOS
## I.12.4 File Names on MS-DOS
## I.12.5 Printing and MS-DOS
## I.12.6 International Support on MS-DOS
## I.12.7 Subprocesses on MS-DOS
