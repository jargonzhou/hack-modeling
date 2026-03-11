# Learning Regular Expressions

terms:
- regular expression
- metacharacters
- text manipulation: search, replace
- regular expression implementation


# 1 Introducing Regular Expressions

Regular expressions: RegEx, regex.
- strings that are used to match and manipulate text.
- are created using the regular expression language.

how regular expression are used:
- search: locate information.
- replace: locate and edit information.

# 2 Matching Single Characters

- matching literal text

special characters: used to identity what is to be searched for.
- `.`: match any character, alphabetic characters, digits and even `.` itself.

metacharacter:
- `\`: backslash

# 3 Matching Sets of Characters

metacharacter:
- `[`, `]`: define a set of characters.
- `^`: negate character set.

examples:
- `[Rr]eg[Ee]x`
- range: `[0-9]`, `[A-Z]`, `[a-z]`, `[A-F]`, `[A-z]`, `[A-Za-z0-9]`
- anything but: `[^0-9]`

# 4 Using Metacharacters

whitespace metacharacters:
- `[\b]`: backspace
- `\f`: form feed
- `\n`: line feed
- `\r`: carriage return
- `\t`: tab
- `\v`: vertical tab
- `\s`: `[\f\n\r\t\v]`
- `\S`: `[^\f\n\r\t\v]`

digit metacharacters:
- `\d`: `[0-9]`
- `\D`: any non-digit, `[^0-9]`

alphanumeric metacharacters:
- `\w`: `[a-zA-Z0-9_]`
- `\W`: `[^a-zA-Z0-9_]`

POSIX character classes:
- `[:alnum:]`: `[a-zA-Z0-9]`
- `[:alpha:]`: `[a-zA-Z]`
- `[:blank:]`: space or table, `[ \t]`
- `[:cntrl:]`: ASCII control characters: 0-31, 127
- `[:digit:]`: `[0-9]`
- `[:graph:]`: same as `[:print:]` but exclude space
- `[:lower:]`: any lowercase letter, `[a-z]`
- `[:print:]`: any printable character
- `[:punct:]`: any character neither `[:alnum:]` or `[:cntrl:]`
- `[:space:]`: any whitespace character include spaces, `[ \f\n\r\t\b]`
- `[:upper:]`: uppercase letter, `[A-Z]`
- `[:xdigit:]`: hexadecimal digit, `[a-fA-F0-9]`

# 5 Repeating Matches

metacharacters:
- `+`: match one or more.
- `*`: match zero or more.
- `?`: match zero or one.
- `{`, `}`: interval
	- exact: `{3}`
	- range: `{2,4}`, `{0,3}`
	- at least: `{3,}`

metacharacters like `*` and `+` are **greedy**: look for the greatest possible match as opposed to the smallest.
**lazy** quantifiers are defined by appending an `?` to the quantifier being used.
- `*?`
- `+?`
- `{n,}?`

# 6 Position Matching

word boundary: 
- `\b`: match the start or end of a word.
- `\B`: not match at a word boundary.

string boundary:
`^`: match start of string.
`$`: match end of string.

multiline mode:
- `(?m)`: enable multiline mode.

# 7 Using Subexpressions

grouping with subexpressions:
- subexpression are enclosed between `(` and `)` characters.
- `|`: the OR operator

nesting subexpressions

# 8 Using Backreferences

- `\1`: a reference back to the subexpression, match the first.
- `\2`: match the second subexpression.
- `\3`, ...: the third and so on.

JavaScript use `\`, Perl use `$`.

perform replace operations: `$1`, ....

converting case:
- `\E`: terminate `\L` or `\U` conversion.
- `\l`: convert next character to lowercase.
- `\L`: convert all characters up to `\E` to lowercase.
- `\u`: convert next character to uppercase.
- `\U`: convert all characters up to `\E` to uppercase.

# 9 Looking Ahead and Behind

look ahead:
- a subexpression preceded by `?=` (lookahead operator), and the text to match follows the = sign.

look behind:
- `?<=`: lookbehind operator.

negate lookaround:
- `(?!)`: negative lookahead
	- `(?=)`: positive lookahead
- `(?<!)`: negative lookbehind
	- `(?<=)`: positive lookbehind

# 10 Embedding Conditions

regular expression conditions are defined using `?`.
- `?`: match the previous character or expression if it exists.
- `?=`, `?<`: match text ahead or behind, if it exists.

backreference conditions: 
- `(?(backreference)true)`
- `(?(backreference)true|false)`: else expression.
- `?(1)` checks to see if backreference 1 exists.

lookaround conditions:
- like backreference conditions, expcept that the backreference is replaced by a complete lookaround expression.

# 11 Regular Expression Solutions to Common Problems

examples:
- north American phone numbers
- U.S. ZIP codes
- Canadian postal codes
- United Kingdom postcodes
- U.S. social security numbers
- IP addresses
- URLs
- Email addresses
- HTML comments
- JavaScript comments
- Credit card numbers

# 12 A. Regular Expression in Popular Applications and Languages

- `grep`:
	- `-E`: use extended regular expressions.
	- `-G`: use basic regular expressions.
	- `P`: use Perl regular expressions.
- Java: `java.util.regex`.
- JavaScript: `String` and `RegEx` objects.
- Microsoft .NET
- Microsoft SQL Server T-SQL
- Microsoft Visual Studio .NET
- MySQL: `REGEXP`.
- Oracle PL/SQL
- Perl
- PHP
- Python: `re` module.