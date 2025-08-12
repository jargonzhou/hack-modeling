# Org Mode
* https://orgmode.org/
* Org-Mode Reference Card

> Org Mode: Your life in plain text
> 
> A GNU Emacs major mode for keeping notes, authoring documents, computational notebooks, literate programming, maintaining to-do lists, planning projects, and more — in a fast and effective plain text system.

Tutorial
- [emacs-org-mode-tutorial](https://github.com/james-stoup/emacs-org-mode-tutorial): A primer for users trying to make sense of Org Mode

# Terminology
- mode
- outliner
- headlines
- visibility cycling
	- subtree
	- global
- sparse trees
- plain lists
	- unordered
	- ordered
	- description
- tables
- hyperlinks
	- internal
	- external
- TODO items
	- multi-state workflow
	- progress logging
	- tracking TODO state changes
	- priority
	- tasks, subtasks
	- checkbox
- tags: ex `:work:`
	- tag group
	- tag search
- properties: ex `:Title: Goldberg Variations`
- timestamp
	- deadline
	- scheduling
	- clock work time
- capture, refile, archive
	- capture templates
- agenda views
	- agenda buffer: with commands
	- agenda files
	- agenda dispatcher
	- weekly/daily agenda
	- global TODO list
	- matching tags and properties
	- search view
- markup
	- paragraphs
	- emphasis, monospace(等宽(字体))
	- LATEX
	- literal examples
	- images
	- footnotes
- exporting
	- export dispatcher
	- table of content(ToC)
	- include files
	- comment lines
	- export: HTML, LATEX, iCalendar
- publishing
- working with source code
	- header arguments
	- evaluate code blocks, results of evaluation
	- export code blocks
	- extract source code
- completion
- structure templates
- clean view: `org-indent-mode`

# Org Mode Compact Guide

## Dates and Times


> Timestamps

**Timestamps** can be used to plan appointments, schedule tasks, set deadlines, track time, and more.
- Plain timestame; Event, Appointment
	- `<2006-11-01 Wed 19:15>`
	- `<2006-11-02 Thu 20:00-22:00>`
	- `<2006-11-03 Fri>`
- Timestamp with repeater interval: `h`, `d`, `w`, `m`, `y`
	- `<2007-05-16 Wed 12:30 +1w>`
- Diary-style expression entries
	- `<\%\%(diary-float t 4 2)>` - omit `\`
- Time range
	- `<2006-11-02 Thu 10:00-12:00>`
- Time/Date range
	- `<2004-08-23 Mon>--<2004-08-26 Thu>`
	- `<2004-08-23 Mon 10:00-11:00>--<2004-08-26 Thu 10:00-11:00>`
- Inactive timestamp
	- `[2006-11-01 Wed]`

> Creating Timestamps

commands ...

> Deadlines and Scheduling

commands ...

- `DEADLINE`
- `SCHEDULED`

> Clocking Work Time

commands ...

- `CLOCK`, `\=>HH:MM` (omit `\`)

# See Also
- [Worg](https://orgmode.org/worg/): a World of Org. It includes tutorials, ideas, code snippets, etc., shared to make your introduction and customization of Org-mode as easy as possible.
	- [scientific papers](https://orgmode.org/worg/org-papers.html)
	- [Org-Mode Reference Card](https://orgmode.org/worg/orgcard.html)
	- Resources
		- Learn Org-Mode
		- Get Help with Org-Mode
		- Use Org-Mode Effectively
		- Dive Deeper into Org-Mode
		- Check Out Third-Party Contributions

- [iCalendar (RFC 5545)](https://icalendar.org/RFC-Specifications/iCalendar-RFC-5545/)
> iCalendar
> iCalendar is a standard method of transferring calendar information between computer systems. The standard allows products from many vendors to transfer calendar information between each other.  iCalendar files typically have the file extension `.ical` `.ics` `.ifb`  or `.icalendar` with a MIME type of `text/calendar`.

