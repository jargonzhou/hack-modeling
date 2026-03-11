# A PlusCal User's Manaual: P-Syntax

Version: 1.8

reserved words
```PlusCal
assert
await
begin
call
define
do
either
else
elsif
end
goto
if
macro
or
print
procedure
process
return
skip
then
variable
variables
when
while
with
```
reserved symbols
```PlusCal
:=
||
```

# 1 Introduction

# 2 Getting Started
## 2.1 Typing the Algorithm
## 2.2 The TLA+ Module
## 2.3 Translating and Executing the Algorithm
## 2.4 Checking the Results
## 2.5 Checking Termination
## 2.6 A Multiprocess Algorithm
## 2.7 Where Labels Must and Can't Go


# 3 The Language
- expressions
- statements
	- assignment: `:=`
	- `if test then <t_clause> else <e_clause> end if;`
	- `either <clause1> or <clause2> .. or <clausen> end either;`
	- `<lb>: while <test> do <body> end while`
	- `await <expr>`, `when <expr>`
	- `with <id \in S> do <body> end with;`
	- `skip;`
	- `print <expr>;`: TLC module
	- `assert <expr>`: TLC module
	- `call`, `return;`
	- `goto <lab>;`
- processes
	- `process <ProcName> \in <IdSet>`
	- `process <ProcName> = <Id>`
- procedures
	- `procedure <PName> (<param1>, ..., <paramn>)`
	- `call <PName> (<expr1>, ..., <exprn>)`
- macros
	- `macro <MName> (<param1>, ..., <paramn>) <body> end macro;`
	- `<MName>(<expr1>, ..., <exprn>)`
- definitions
	- `define <body> end define;`
- labels
	- placement rules
	- implicit labels: `Done`, `Error`
- translation's definitions and declarations

# 4 Checking the Algorithm
- Running the Translator
- Specifying the Constants
- Constraints
- Understanding TLC's Output
- Invariance Checking
- Termination, Liveness, and Fairness

Termination is a special case of a general class of properties called *liveness* properties, which assert that something must eventually happen.
An algorithm satisfies a liveness property only under some assumptions, usually *fairness assumptions on actions*.
In a PlusCal algorithm, there is an action corresponding to each label. Execution of that action consists of executing all code from that label to the next.
A action is **enabled** iff it can be executed.
```TLA+
(* code within a process *)
a: y := 42;
   z := y + 1;
b: await x > self;
   x := x - 1;
c: \* ...
```
An execution of action `a` consists of executing the assignment to `y` and `z`.
The action is enabled iff control in the process is at `a`.
An execution of action `b` decrements `x` by 1.
It is enabled iff control is at `b` and the value of `x` is greater than the process's identifier `self`.

An action like `a` that is enabled iff control is at that label is said to be **non-blocking**.
An action like `b` that is not non-blocking is said to be **blocking**.

*Fairness for a non-blocking actions* means that the process cannot stop at that action.
Thus, fairness at `a` means that *if control in the process is at `a`, then the process must eventually execute action `a`*.

There are 2 kinds of fairness conditions for blocking actions.
**Weak fairness** of an action $\alpha$ means that a process cannot halt at $\alpha$ if $\alpha$ *remains forever enabled*.
For example, weak firness of action `b` means that *if `x > self` remains true while the process is at `b`, then action `b` is eventually executed*.
**Strong fairness** of $\alpha$ means that, in addition to a process not being able to halt at $\alpha$ if $\alpha$ remains true forever, it can't halt if $\alpha$ *keeps being disabled and subsequently enabled*.
For example, strong fairness of action `b` impilies that *process `self` cannot halt at `b` as long as `x > self` either remains true or keeps becoming true, even if it also keeps becoming false*.

For a non-blocking action, weak and strong fairness are equivalent.

`fair process` asserts that all actions of the process are, by default, *weakly fair*.
The default fairness condition of an action of the process can be modified by adding `+` or `-` after its label.
writing `a:+` asserts that action `a` is strongly fair.
writing `a:-` asserts that action `a` satisfies no fairness condition.

`fair+ process` asserts that all actions of the process are *strongly fair* by default.
adding `-` after a label in the process asserts that the action satisfies no fairness condition.
adding `+` after a label in a `fair+` process has no effect.

A process that is not a `fair` or `fair+` process is call an **unfair** process and has no fairness assumptions on its actions.
adding `+` or `-` after a label in such a process has no effect.

> TODO: translator options

The liveness properties we want an algorithm to satisfy can be specified as *temporal formulas* using the TLA+ temporal operators used to express fairness and liveness (Section 5.10).

> TODO: temporal formulas

- Additional TLC Features
	- Deadlock Checking
	- Multithreading
	- Symmetry


# 5 TLA+ Expressions and Definitions
- Numbers
- Strings
- Boolean Operators
- Sets
- Functions
- Records
- The Except Construct
- Tuples and Sequences
- Miscellaneous Constructs
- Temporal Operators
	- Fairness
	- Liveness
	- One Algorithm Implementing Another
- TLA+ Definitions

# 6 A. The Grammar
> P.57

the BNF grammar of PlusCal
# 7 B. The TLA+ Translation
the TLA+ translation of a PlusCal algorithm
# 8 C. Translator Options
Some translator options can be specified in the module file with an `options ` statement:
- either in a comment or - P.11
- before or after the module
```TLA+
PlusCal options (<list-of-options>)

\* ex
(* PlusCal options (-lineWidth 120) *)
```

- options that may appear in an `options statement`
- options that can be specified using the Spec Explorer
- options for command-line use only
# 9 Useful Tables
> P.70

Table 1: The operators of TLA+.
- Logic
- Sets
- Functions
- Records
- Tuples
Table 2: Miscellaneous consttucts.
- `IF-THEN-ELSE`
- `CASE-[OTHER]`
- `LET-IN`
- `/\`
- `\/`
Table 3: Temporal operators.
- `\A`
- `\E`
- weak fairness
	- $WF_{e}(A)$
	- PlusCal `fair`
- strong fairness
	- $SF_{e}(A)$
	- PlusCal `fair+`
- `F ~> G` 
Table 4: User-definable operator symbols.
Table 5: The ASCII representations of typeset symbols.
