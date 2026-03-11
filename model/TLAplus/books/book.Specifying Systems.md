# Specifying Systems
* Leslie Lamport. **Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers**. Pearson Education: 2002.

Part I Getting Started
- 1 A Little Simple Math
- 2 Specifying a Simple Clock
- 3 An Asynchronous Interface
- 4 A FIFO
- 5 A Caching Memory
- 6 Some More Math
- 7 Writing a Specification: Some Advice
Part II More Advanced Topics
- 8 Liveness and Fairness
- 9 Real Time
- 10 Composing Specifications
- 11 Advanced Examples
Part III The Tools
- 12 The Syntactic Analyzer
- 13 The TLATEX Typesetter
- 14 The TLC Model Checker
Part IV The TLA+ Language
- 15 The Syntax of TLA+
- 16 The Operators of TLA+
- 17 The Meaning of a Module
- 18 The Standard Modules

# 1 A Little Simple Math

## 1.1 Propositional Logic
boolean values: $\texttt{TRUE}$, $\texttt{FALSE}$.
operators:
- $\wedge$: conjunction (and). $F \wedge G$ equals $\texttt{TRUE}$ iff both $F$ and $G$ equal $\texttt{TRUE}$.
- $\vee$: disjunction (or). $F \vee G$ equals $\texttt{TRUE}$ iff $F$ or $G$ equal $\texttt{TRUE}$.
- $\neg$: negation (not). $\neg F$ equals $\texttt{TRUE}$ iff $F$ equals $\texttt{FALSE}$.
- $\implies$: implication (implies). $F \implies G$ equals $\texttt{TRUE}$ iff $F$ equals $\texttt{FALSE}$ or $G$ equals $\texttt{TRUE}$.
- $\equiv$: equivalence (is equivalent to). $F \equiv G$ equals $\texttt{TRUE}$ iff both equal $\texttt{TRUE}$ or both equal $\texttt{FALSE}$.
## 1.2 Sets
$x \in S$ means that $x$ is an element of $S$.
$\{1, 2, 3\}$: a set contains 3 elements $1$, $2$ and $3$.
common operations:
- $\cap$: intersection. $S \cap T$ is the set of elements in both $S$ and $T$.
- $\cup$: union. $S \cup T$ is the set of elements in $S$ or $T$.
- $\subseteq$: subset. $S \subseteq T$ is true iff every element of $S$ is an element of $T$.
- $\setminus$: set difference. $S \setminus T$ is the set of elements in $S$ that are not in $T$.
## 1.3 Predicate Logic
quantifiers:
- $\forall$: universal quantification (for all). $\forall x \in S : F$ asserts that formula $F$ is true for every element $x$ in the set $S$.
- $\exists$: existential quantification (there exists). $\exists x \in S : F$ asserts that formula $F$ is true for at least one element $x$ in $S$.

$$
\begin{align}
(\exists x \in S : F) & \equiv \neg (\forall x \in S : \neg F)         \\
(\forall x \in S : F) & \equiv (\forall x : (x \in S) \implies F)      \\
(\exists x \in S : F) & \equiv (\exists x : (x \in S) \wedge F)        \\
(\forall x \in S : F) \wedge (\forall x \in S : G) & \equiv (\forall x \in S : F \wedge G) \\
(\exists x \in S : F) \vee (\exists x \in S : G) & \equiv (\exists x \in S : F \vee G)
\end{align}
$$

abbreviations:
- $\forall x \in S, y \in T : F$ means $\forall x \in S : (\forall y \in T : F)$.
- $\exists w,x,y,z \in S : F$ means $\exists w \in S : (\exists x \in S : (\exists y \in S : (\exists z \in S : F)))$.

## 1.4 Formulas and Language
In this book, you are entering the realm of logic, where a formula is a noun.

# 2 Specifying a Simple Clock
## 2.1 Behaviors
Formally, we define a **behavior** to be a sequence of states, where a *state* is an assignment of values to variables.
## 2.2 An Hour Clock

$hr$: variable represent the clock's display.
a typical behavior of the clock:
$$
[hr = 11] \to [hr = 12] \to [hr = 1] \to [hr = 2] \to \cdots
$$

To specify the hour clock, we describe all its possible behaviors:
- **initial predicate** $HCini$: specify the possible initial values of variables, here $hr$.
- **next-state relation** $HCnxt$: specify how the values of variables can change in any step.

we let $hr$ represent the value of $hr$ in the old state and $hr'$ represent its value in the new state. (The $'$ in $hr'$ is read **prime**.)
$$
\begin{align}
HCini & \triangleq hr \in \{ 1, \cdots, 12 \} \\
HCnxt & \triangleq hr' = \texttt{IF} \  hr \neq 12 \ \texttt{THEN} \ hr + 1 \ \texttt{ELSE} \ 1
\end{align}
$$

temporal formula $\Box F$ asserts that formula $F$ is always true. for example $\Box HCnxt$ is the assertion that $HCnxt$ is true for every step in the behavior.

specify the system in a single forumal: 
$$
HCini \wedge \Box HCnxt
$$

a larger system: the hour disply of a weather station that displays the current hour $hr$ and temperature $tmp$

a sample behavior of this system:
$$
\begin{bmatrix} hr = 11 \\ tmp = 23.5 \end{bmatrix} \to
\begin{bmatrix} hr = 12 \\ tmp = 23.5 \end{bmatrix} \to
\begin{bmatrix} hr = 12 \\ tmp = 23.4 \end{bmatrix} \to \\
\begin{bmatrix} hr = 12 \\ tmp = 23.3 \end{bmatrix} \to
\begin{bmatrix} hr = 1  \\ tmp = 23.3 \end{bmatrix} \to \cdots
$$

a formula that describes any hour clock must allow steps that leave $hr$ unchanged, in other words, $hr' = hr$ steps. 
These are called **stuttering steps** of the clock.
$$
HCini \wedge \Box (HCnxt \vee (hr' = hr))
$$

in TLA, use $[HCnxt]_{hr}$ stand for $HCnxt \vee (hr' = hr)$:
$$
HC \triangleq HCini \wedge \Box [HCnxt]_{hr}
$$

## 2.3 A Closer Look at the Specification
A temporal formula satisfied by every behavior is called a **theorem**.
## 2.4 The Specification in TLA+
2 version of the hour-clock specification: 
- the ASCII version 
- the typeset version

symbols mapping:
- $\Box$: `[]`.
- $\neq$: `#`, `/=`.
- $\in$: `\in`.
- $\triangleq$: `==`.

the ASCII version:
```TLA+
---------------------- MODULE HourClock ----------------------
EXTENDS Naturals
VARIABLE hr
HCini == hr \in (1 .. 12)
HCnxt == hr' = IF hr ## 2.12 THEN hr + 1 ELSE 1
HC == HCini /\ [][HCnxt]_hr
--------------------------------------------------------------
THEOREM HC => []HCini
==============================================================
```

the typeset version:
$$
\begin{array}{l}
\begin{array}{l}
\texttt{MODULE}    & HourClock \\
\texttt{EXTENDS}   & Naturals \\
\texttt{VARIABLE} & hr \\
\end{array} \\
\begin{array}{lll}
HCini & \triangleq hr \in (1 .. 12) \\
HCnxt & \triangleq hr' = \texttt{IF} \ hr \neq 12 \ \texttt{THEN} \ hr + 1 \ \texttt{ELSE} \ 1 \\
HC    & \triangleq HCini \wedge \Box [HCnxt]_{hr}
\end{array} \\
\\
\begin{array}{l}
\texttt{THEOREM}  \ HC \implies \Box HCini
\end{array}
\end{array}
$$
## 2.5 An Alternative Specification
```TLA+
---------------------- MODULE HourClock ----------------------
EXTENDS Naturals
VARIABLE hr
HCini == hr \in (1 .. 12)
HCnxt == hr' = (hr % 12) + 1
HC == HCini /\ [][HCnxt]_hr
--------------------------------------------------------------
THEOREM HC => []HCini
==============================================================
```


# 3 An Asynchronous Interface

> [!example] an interface for transmitting data between asynchronous devices.
Data is send on `val`, and the `rdy` and `ack` lines are used for synchronization.
The sender must wait for an `ack` for one data item before it can send the next.
```
+--------+        +--------+
|        |--val-->|        |
|        |--rdy-->|        |
| Sender |        |Receiver|
|        |        |        |
|        |<--ack--|        |
+--------+        +--------+
```

a sample behavior:

$$
\begin{bmatrix} val = 26 \\ rdy = 0 \\ ack = 0 \end{bmatrix} \overset{Send \ 37}{\to}
\begin{bmatrix} val = 37 \\ rdy = 1 \\ ack = 0 \end{bmatrix} \overset{Ack}{\to}
\begin{bmatrix} val = 37 \\ rdy = 1 \\ ack = 1 \end{bmatrix} \overset{Send \ 4}{\to} \\
\begin{bmatrix} val = 4  \\ rdy = 0 \\ ack = 1 \end{bmatrix} \overset{Ack}{\to}
\begin{bmatrix} val = 4  \\ rdy = 0 \\ ack = 0 \end{bmatrix} \overset{Send \ 19}{\to}
\begin{bmatrix} val = 19 \\ rdy = 1 \\ ack = 0 \end{bmatrix} \overset{Ack}{\to} \cdots
$$

A *specification* is an abstraction, it describes some aspects of the system and ignores others.
When writing a specification, you must first choose the abstraction.
In a TLA+ specification, this means choosing the variables that represent the system's state and the granularity of the steps that change those variables' value. examples:
- should the `rdy` and `ack` lines be represented as separate variables or as a single variable?
- should `val` and `rdy` change in one step, two steps, or an arbitrary number of steps?
## 3.1 The First Specification
some terms:
- a **state function** is an ordinary expression (one with no prime or $\Box$) that can contain variables and constants.
- a **state predicate** is a boolean-valued state function.
- an **invariant** $Inv$ of a specification $Spec$ is a state predicate such that $Spec \implies \Box Inv$ is a theorem.
- a variable $v$ has **type** $T$ in a specification $Spec$ iff $v \in T$ is an invariant of $Spec$.

$$
\begin{array}{l}
\begin{array}{l}
\texttt{MODULE} & AsynchInterface \\
\texttt{EXTENDS} & Naturals \\
\texttt{CONSTANT} & Data \\
\texttt{VARIABLES} & val, rdy, ack \\
\end{array} \\
\begin{array}{lll}
TypeInvariant & \triangleq & \wedge \ val \in Data \\
                          && \wedge \ rdy \in \{0, 1\} \\
                          && \wedge \ ack \in \{0, 1\} \\
\\
Init          & \triangleq & \wedge \ val \in Data \\
                          && \wedge \ rdy \in \{0, 1\} \\
                          && \wedge \ ack = rdy \\       
Send          & \triangleq & \wedge \ rdy = ack \\
                          && \wedge \ val' \in Data \\
                          && \wedge \ rdy' = 1 - rdy \\
                          && \wedge \ \texttt{UNCHANGED} \ ack \\
Rcv           & \triangleq & \wedge \ rdy \neq ack \\
                          && \wedge \ ack' = 1 - ack \\
                          && \wedge \ \texttt{UNCHANGED} \ \left\langle val, rdy \right\rangle \\
Next          & \triangleq & Send \vee Rcv \\
Spec          & \triangleq & Init \wedge \Box [Next]_{\left\langle val, rdy, ack \right\rangle} \\
\end{array} \\
\\
\begin{array}{l}
\texttt{THEOREM}  \ Spec \implies \Box TypeInvariant
\end{array}
\end{array}
$$

## 3.2 Another Specification
A system might use several different instances of the interface.
We replace the three variables $val$, $rdy$, $ack$ with a single variable $chan$ (shor for **channel**).
TLA+ provides *records*.
$$
\begin{array}{l}
\begin{array}{l}
\texttt{MODULE}   & Channel \\
\texttt{EXTENDS}  & Naturals \\
\texttt{CONSTANT} & Data \\
\texttt{VARIABLE} & chan \\
\end{array} \\
\begin{array}{lll}
TypeInvariant & \triangleq & chan \in [val : Data, rdy : \{0, 1\}, ack: \{0, 1\}] \\
\\
Init          & \triangleq & \wedge TypeInvariant \\
                          && \wedge \ chan.ack = chan.rdy \\       
Send(d)       & \triangleq & \wedge \ chan.rdy = chan.ack \\
                          && \wedge \ chan' = [chan \ \texttt{EXCEPT} \ !.val = d, !.rdy = 1 - @] \\
Rcv           & \triangleq & \wedge \ chan.rdy \neq chan.ack \\
                          && \wedge \ chan' = [chan \ \texttt{EXCEPT} \ !.ack = 1 - @] \\
Next          & \triangleq & (\exists d \in Date : Send(d)) \vee Rcv \\
Spec          & \triangleq & Init \wedge \Box [Next]_{chan} \\
\end{array} \\
\\
\begin{array}{l}
\texttt{THEOREM}  \ Spec \implies \Box TypeInvariant
\end{array}
\end{array}
$$
- $[chan \ \texttt{EXCEPT} \ !.val = d, !.rdy = 1 - @]$ equals to $[chan \ \texttt{EXCEPT} \ !.val = d, !.rdy = 1 - chan.rdy]$, which equals to $[val \mapsto d, rdy \mapsto 1 - chan.rdy, ack \mapsto chan.ack]$.
## 3.3 Types: A Reminder
Why not add a formal type system to TLA+?
The question is addressed further in Section 6.2.

TLA+ is an *untyped* language.
Type correctness is just a name for a certain invariance property.
## 3.4 Definitions
If $Id$ is a simple identifier like $Init$ or $Spec$, then the **definition** $Id \triangleq exp$ defines $Id$ to be synonymous with the expression $exp$.
Replacing $Id$ by $exp$, or vice-versa, in any expression does not change the meaning of that expression.
This replacement must be done after the expression is parsed, not in the *raw input*.

**operators**:
$$
Id(p_1, \cdots, p_n) \triangleq exp
$$

here $p_i$ are distinct identifiers, and $exp$ is an expression.

use the term **symbol** to mean an identifier like $Send$ or an operator symbol like $+$.
Every symbol that is used in a specification must either be a built-in operator of TLA+ (like $\in$) or it must be declared or defined.
Every symbol declaration or definition has a **scope** within which the symbol may be used:
- The scope of a `VARIABLE` or `CONSTANT` declaration, and of a definition, is the part of the module that follows it.
- The statement `EXTEDNS Naturals` extends the scope of symbols like `+` defined in the `Naturals` module to the `Channel` module.
- $Id(p_1, \cdots, p_n) \triangleq exp$ implicitly includes a declaration of the identifier $p_1, \cdots, p_n$ whose scope is the expression $exp$.
- $\exists v \in S : exp$ has a declaration of $v$ whose scope is the expression $exp$.

a symbol cannot be declared or defined if it already has a meaning, $(\exists v \in S : (exp1 \wedge \exists v \in T : exp2))$ is illegal.

## 3.5 Comments

- end-of-line comment: `\* ...`.
- block comment: `(* ... *)`.

example:
```TLA+
---------------------- MODULE HourClock ----------------------
(********************************************************)
(* This module specifies a digital clock that displays  *)
(* the current hour. It ignores real time, not          *)
(* specifying when the display can change.              *)
(********************************************************)
EXTENDS Naturals
VARIABLE hr         \* Variable hr represents the display.
HCini == hr \in (1 .. 12)   \* Initially, hr can have any
                            \* value from 1 through 12.
HCnxt (* This is a weird place for a comment. *) ==
(*************************************************)
(* The value of hr cycles from 1 through 12.     *)
(*************************************************)
    hr' = IF hr # 12 THEN hr + 1 ELSE 1
HC == HCini /\ [][HCnxt]_hr
(* The complete spec. It permits the clock to stop. *)
--------------------------------------------------------------
THEOREM HC => []HCini \* Type-correctness of the spec.
==============================================================
```

$$
\begin{array}{l}
\bbox[lightgray, 4px]{
\begin{aligned}
&\text{This module specifies a digital clock that displays the current hour.} \\
&\text{It ignores real time, not specifying when the display can change. }
\end{aligned}} \\
\begin{array}{l}
\texttt{MODULE}    & HourClock \\
\texttt{EXTENDS}   & Naturals \\
\texttt{VARIABLE} & hr \ \bbox[lightgray, 4px]{\text{Variable hr represents the display.}}\\
\end{array} \\
\begin{array}{lll}
HCini & \triangleq hr \in (1 .. 12) \ \bbox[lightgray, 4px]{\text{Initially, hr can have any value from 1 through 12.}} \\
HCnxt  & \triangleq \\
&\bbox[lightgray, 4px]{\text{The value of hr cycles from 1 through 12.}} \\
&hr' = \texttt{IF} \ hr \neq 12 \ \texttt{THEN} \ hr + 1 \ \texttt{ELSE} \ 1 \\
HC    & \triangleq HCini \wedge \Box [HCnxt]_{hr} \\
& \bbox[lightgray, 4px]{\text{The complete spec. It permits the clock to stop.}} 
\end{array} \\
\\
\begin{array}{l}
\texttt{THEOREM}  \ HC \implies \Box HCini \\ \bbox[lightgray, 4px]{\text{Type-correctness of the spec.}} 
\end{array}
\end{array}
$$

The *module structure* allow us to choose the order in which a specification is read.
example: split the `HourClock` module into 3 modules:
- `HCVar`: a module that declares the variable `hr`.
- `HCActions`: a module that `EXTENDS` modules `Naturals` and `HCVar` and defines `HCini` and `HCnxt`.
- `HCSpec`: a module that `EXTENDS` module `HCActions`, defines formula `HC`, and asserts the type-correctness theorem.

The `EXTENDS` relation implies a logical ordering of the modules.


# 4 A FIFO
A FIFO buffer is a device with which a sender process transmits a sequence of values to a receiver.
The send and receiver use two channels $in$ and $out$, to communicate with the buffer.
Values are send over $in$ and $out$ using the asynchronous protocol specified by the `Channel` module.

```
+--------+                         +--------+
|        |       +--------+        |        |
|        |       |        |        |        |
| Sender |--in-->| Buffer |--out-->|Receiver|
|        |       |        |        |        |
|        |       +--------+        |        |
+--------+                         +--------+
```

## 4.1 The Inner Specification

the `Sequences` module:

- sequence example: `<3, 2, 1>`
- `Seq(S)`
- `Head(s)`
- `Tail(s)`
- `Append(s, e)`
- `s \o t`
- `Len(s)`

```
---------------------- MODULE InnerFIFO ----------------------
EXTENDS Naturals, Sequences
CONSTANT Message
VARIABLES in, out, q
InChan  == INSTANCE Channel WITH Data <- Message, chan <- in
OutChan == INSTANCE Channel WITH Data <- Message, chan <- out

Init          == /\ InChan!Init
                 /\ OutChan!Init
                 /\ q = <>
TypeInvariant == /\ InChan!TypeInvariant
                 /\ OutChan!TypeInvariant
                 /\ q \in Seq(Message)
SSend(msg)    == /\ InChan!Send(msg)            \* Send msg on channel in.
                 /\ UNCHANGED <out, q>
BufRcv        == /\ InChan!Rcv                  \* Receive message from channel in
                 /\ q' = Append(q, in.val)      \* and append it to tail of q.
                 /\ UNCHANGED out
BufSend       == /\ q /= <>                     \* Enabled only if q is nonempty.
                 /\ OutChan!Send(Head(q))       \* Send Head(q) on channel out
                 /\ q' = Tail(q)                \* and remove it from q.
                 /\ UNCHANGED in
RRcv          == /\ OutChan!Rcv                 \* Receive message from channel out.
                 /\ UNCHANGED <in, q>
Next          == \/ \E msg \in Message : SSend(msg)
                 \/ BufRcv
                 \/ BufSend
                 \/ RRcv
Spec          == Init /\ [][Next]_<in, out, q>
--------------------------------------------------------------
THEOREM Spec => []TypeInvariant
==============================================================
```

## 4.2 Instantiation Examined
## 2.1 Instantiation Is Substitution

```TLA+
InChan == INSTANCE Channel WITH Data <- Message, chan <- in

IM == INSTANCE M WITH p1 <- e1, ... , pn <- en
```

let $\Sigma$ be a symbol defined in module $M$ and let $d$ be its real definition.
The `INSTANCE` statement defines $IM!\Sigma$ to have as its real definition the expression obtained from $d$ by replacing all instances of $p_i$ by the expression $e_i$ for each $i$.
The definition of $IM!\Sigma$ must contain only the parameters (declared constants and variables) of the current module, not the ones of module $M$.

## 2.2 Parametrized Instantiation

```TLA+
Chan(ch) == INSTANCE Channel WITH Data <- Message, chan <- ch
```

## 2.3 Implicit Substitutions

```TLA+
InChan == INSTANCE Channel WITH Data <- Data, chan <- in
InChan == INSTANCE Channel WITH chan <- in
```

## 2.4 Instantiation Without Renaming

```TLA+
INSTANCE Channel WITH Data <- D, chan <- x
```

## 4.3 Hiding the Queue

```TLA+
---------------------- MODULE FIFO ----------------------
CONSTANT Message
VARIABLES in, out
Inner(q) == INSTANCE InnerFIFO
Spec == \E q : Inner(q)!Spec
==============================================================
```

## 4.4 A Bounded FIFO

```TLA+
---------------------- MODULE BoundedFIFO ----------------------
EXTENDS Naturals, Sequences
VARIABLES in, out
CONSTANT Message, N
ASSUME (N \in Nat) /\ (N > 0)
Inner(q) == INSTANCE InnerFIFO
BNext(q) == /\ Inner(q)!Next
            /\ Inner(q)!BufRcv => (Len(q) < N)
Spec == \E q : Inner(q)!Init /\ [][BNext(q)]_<in, out, q>
==============================================================
```

here `ASSUME (N \in Nat) /\ (N > 0)` asserts that we are assuming `N` is a positive natural number.

## 4.5 What We're Specifying

The sender and receiver are not part of the FIFO buffer, they form its **environment**.

```TLA+
Next    == SysNext \/ EnvNext
SysNext == BufRcv \/ BufSend
EnvNext == (\E msg \in Message : SSend(msg)) \/ RRcv
```

A formual which describes the correct behavior of both the system and its environment, is called a **closed-system** or **complete-system** specification.

An *open-system* specification is one that describes only the correct behavior of the system.
Section 10.7 explains how to write open-system specifications.


# 5 A Caching Memory

```
+-----------+    +--------+
| Processor |<-->|        |    +--------+
+-----------+    |        |    |        |
                 | memInt |<-->| MEMORY |
+-----------+    |        |    |        |
| Processor |<-->|        |    +--------+
+-----------+    +--------+
```

## 5.1 The Memory Interface



The expression $\texttt{CHOOSE} x : F$ equals an arbitrary chosen value $x$ that satisfies the formula $F$.

## 5.2 Functions
## 5.3 A Linearizable Memory
## 5.4 Tuples as Functions
## 5.5 Recursive Function Definitions
## 5.6 A Write-Through Cache
## 5.7 Invariance
## 5.8 Proving Implementation


# 6 Some More Math
## 6.1 Sets

- $\texttt{UNION} \ S$: the union of the element of $S$.
- $\texttt{SUBSET} \ S$: the set of all subsets of $S$.
- $\{ x \in S : p \}$: the subset of $S$ consisting of all elements $x$ satisfying property $p$. example: $\{ n \in Nat : n \% 2 = 1 \}$ is the set of odd natural numbers.
- $\{ e : x \in S \}$: the set of elements of the form $e$, for all $x$ in the set $S$. example: $\{2 \times n + 1 : n \in Nat \}$ is the set of odd natural numbers.

the `FiniteSets` modules:

- $\texttt{Cardinality}(S)$ returns the number of elements in set $S$, if $S$ is a finite set.
- $\texttt{IsFiniteSet}(S)$ returns true iff $S$ is a finite set.

## 6.2 Silly Expressions

$$
\forall x \in Real : (x \neq 0) \implies (x \times (3 / x) = 3)
$$

here $Real$ is the set of all real numbers.

## 6.3 Recursion Revisited

the factorial function $fact$:

$$
\begin{array}{l}
fact[n] & = \texttt{IF} \ n = 0 \ \texttt{THEN} \ 1 \ \texttt{ELSE} \ n \times fact[n-1], \ \text{for all} \ n \in Nat \\
fact[n] & = [n \in Nat \mapsto \ \texttt{IF} \ n = 0 \ \texttt{THEN} \ 1 \ \texttt{ELSE} \ n \times fact[n-1]]
\end{array}
\\
\begin{array}{ll}
fact    & \triangleq \texttt{CHOOSE} \ fact : \\
        & fact = [n \in Nat \mapsto \ \texttt{IF} \ n = 0 & \texttt{THEN} \ 1 \\
        && \texttt{ELSE} \ n \times fact[n-1]] \\
fact[n \in Nat] & \triangleq \texttt{IF} \ n = 0 \ \texttt{THEN} \ 1 \ \texttt{ELSE} \ n \times fact[n-1]
\end{array}
$$

$f[x \in S] \triangleq e$ is an abbreviation for $f \triangleq \texttt{CHOOSE} \ f : f = [x \in S \mapsto e]$.

TLA+ allows the apparent circularity of a recursive function definition, it does *not* allow circular definitions in which two or more functions are defined a terms of one another.

not allowd:

$$
\begin{array}{l}
f[n \in Nat] & \triangleq \texttt{IF} \ n = 0 \ \texttt{THEN} \ 17 \ \texttt{ELSE} \ f[n-1] \times g[n] \\
g[n \in Nat] & \triangleq \texttt{IF} \ n = 0 \ \texttt{THEN} \ 42 \ \texttt{ELSE} \ f[n-1] + g[n-1]
\end{array}
$$

allowed:

$$
\begin{array}{l}
mr[n \in Nat] & \triangleq \\
              & [f \mapsto \texttt{IF} \ n = 0 \ \texttt{THEN} \ 17 \ \texttt{ELSE} \ mr[n-1].f \times mr[n].g \\
              & g \mapsto \texttt{IF} \ n = 0 \ \texttt{THEN} \ 42 \ \texttt{ELSE} \ mr[n-1].f + mr[n-1].g] \\
\\
f[n \in Nat] & \triangleq mr[n].f \\
g[n \in Nat] & \triangleq mr[n].g
\end{array}
$$

## 6.4 Functions versus Operators

$fact$ is a **function**, $Tail$ is an **operator**:

$$
\begin{array}{l}
Tail(s)         & \triangleq [i \in 1..(Len(s)-1) \mapsto s[i+1]] \\
fact[n \in Nat] & \triangleq \texttt{IF} \ n = 0 \ \texttt{THEN} \ 1 \ \texttt{ELSE} \ n \times fact[n-1]
\end{array}
$$

differences:

- A function by itself is a complete expression that denotes a value, but an operator is not.
- Unlike an operator, a function must have a domain, which is a set.
- Unlike a function, an operator cannot be defined recursively.
- An operator can take an operator as an argument.
- TLA+ does not permit to define infix functions.

$$
\begin{array}{l}
& IsPartialOrder(R(\_, \_), S) \triangleq \\
& \quad \wedge \forall x,y,z \in S : R(x, y) \wedge R(y, z) \implies R(x, z) \\
& \quad \wedge \forall x \in S : \neg R(x, x) \\
\\
& IsPartialOrder(\_ \prec \_, S) \triangleq \\
& \quad \wedge \forall x,y,z \in S : x \prec y \wedge y \prec z \implies x \prec z) \\
& \quad \wedge \forall x \in S : \neg x \prec x
\end{array}
$$

## 6.5 Using Functions

$$
\begin{array}{l}
f' = [i \in Nat \mapsto i + 1] \\
\forall i \in Nat : f'[i] = i + 1
\end{array}
$$

When writing specifications, we almost always want to specify the new value of a varaible $f$ rather than the new values of $f[i]$ for all $i$ in some set.

## 6.6 Choose

The most common use for the $\texttt{CHOOSE}$ operator is to *name* a uniquely specified value. 
example: the `Reals` module defines division on the set $Real$ of real numbers by

$$
a / b \triangleq \texttt{CHOOSE} \ c \in Real : a = b \times c
$$

$(x = \texttt{CHOOSE} \ n : n \in Nat) \wedge \Box[x' = \texttt{CHOOSE} \ n : n \in Nat]_x$ allows a single behavior.

$(x \in Nat) \wedge \Box [x' \in Nat]_x$ allows all behaviors in which $x$ is always a natural number.



# 7 Writing a Specification: Some Advice
## 7.1 Why Specify

The purpose of writing a specification is to help avoid errors:

- writing a TLA+ specification can help the design process.
- a TLA+ specification can provide a clear, concise way of communicating a design.
- a TLA+ specification is a formal description to which tools can be applied to help find errors in the design and to help in testing the system.

## 7.2 What to Specify

A specification is a mathematical model of a particular view of some part of a system.
When writing a specification, the first thing you must choose is exactly what part of the system you want to model.

You should specify those parts of the system for which a specification is most likely to reveal errors.
TLA+ is particularly effective at revealing *concurrency errors*, ones taht arise through the interaction of asynchronous components.

## 7.3 The Grain of Atomicity

The most important aspect of the level of abstraction is *the grain of atomicity*, the choice of what system changes are represented as a single step of a behavior.

the TLA+ **action-composition operator** $\cdot$:
$A \cdot B$ is the action defined by letting $s \to t$ be an $A \cdot B$ step iff there exists a status $u$ such that $s \to u$ is an $A$ step and $u \to t$ is a $B$ step.

When determining the grain of atomicity, we must decide whether to represent the execution of an operation as a single step or as a sequence of steps, each corresponding to the execution of a suboperation.

example: an operation consisting of two suboperations that are executed sequentially, where those suboperations are described by the two actions $R$ and $L$. 
executing $R$ enables $L$ and disables $R$.
When the operation's execution is represented by *a single step*, the operation is described with the action $R \cdot L$.
When the operation's execution is represented by *two steps*, the operation is described with the action $R \vee L$.

Let $S1$ be the coarser-grained specification in which it is executed as a single $R \cdot L$ step,
$S2$ be the finer-grained specification in which the operation is executed in two steps.

Specification $S1$ requires that each $R$ step to be followed immediately by an $L$ step, while $S2$ allows behaviors in which other steps come between the $R$ and $L$ steps.
The additional behaviors allowed by $S2$ are *not important* if the actual system executions they describe are also described by behaviors allowed by $S1$.

The actions $A$ and $B$ **commute** iff $A \cdot B$ is equivalent to $B \cdot A$.

## 7.4 The Data Structures

Another aspect of a specification of a specification's level of abstraction is the accuracy with which it describes the system's data structures.

A precise description of the layout of procedure arguments will help prevent errors caused by misunderstandings about that layout, but at the cost of complicating the program interface's specification.

If the purpose of the specification is to catch errors caused by the asynchronous interaction of concurrently executing components, then detailed descriptions of data structures will be a needless complication.

## 7.5 Writing the Specification

steps:

1. pick the variables and define the type invariant and initial predicate.
2. write the next-state action, which forms the bulk of the specification.
3. write the temporal part of the specification.
4. assert theorems about the specification.

## 7.6 Some Further Hints

suggestions:

- don't be too clever.
- a type invariant is not an assumption.
- don't be too abstract.
- don't assume values that look different are unequal.
- move quantification to the outside.
- prime only what you mean to prime.
- write comments as comments.

## 7.7 When and How to Specify

Making specification part of the design process can improve the design.

Some system functionality will at first be omitted; it can be included later by adding new disjuncts to the next-state action.

# 8 Liveness and Fairness
## 8.1 Temporal Formulas
## 8.2 Temporal Tautologies
## 8.3 Temporal Proof Rules
## 8.4 Weak Fairness
## 8.5 The Memory Specification
### 8.5.1 The Liveness Requirement
### 8.5.2 Another Way to Write It
### 8.5.3 A Generalization
## 8.6 Strong Fairness
## 8.7 The Write-Through Cache
## 8.8 Quantification
## 8.9 Temporal Logic Examined
### 8.9.1 A Review
### 8.9.2 Machine Closure
### 8.9.3 Machine Closure and Possibility
### 8.9.4 Refinement Mappings and Fairness
### 8.9.5 The Unimportance of Liveness
### 8.9.6 Temporal Logic Considered Confusing

# 9 Real Time
## 9.1 The Hour Clock Revisited
## 9.2 Real-Time Specifications in General
## 9.3 A Real-Time Caching Memory
## 9.4 Zeno Specifications
## 9.5 Hybrid System Specifications
## 9.6 Remarks on Real Time

# 10 Composing Specifications
## 10.1 Composing Two Specifications
## 10.2 Composing Many Specifications
## 10.3 The FIFO
## 10.4 Composition with Shared State
### 10.4.1 Explicit State Changes
### 10.4.2 Composition with Joint Actions
## 10.5 A Brief Review
### 10.5.1 A Taxonomy of Composition
### 10.5.2 Interleaving Reconsidered
### 10.5.3 Joint Actions Reconsidered
## 10.6 Liveness and Hiding
### 10.6.1 Liveness and Machine Closure
### 10.6.2 Hiding
## 10.7 Open-System Specifications
## 10.8 Interface Refinement
### 10.8.1 A Binary Hour Clock
### 10.8.2 Refining a Channel
### 10.8.3 Interface Refinement in General
### 10.8.4 Open-System Specifications
## 10.9 Should You Compose?

# 11 Advanced Examples
## 11.1 Specifying Data Structures
### 11.1.1 Local Definitions
### 11.1.2 Graphs
### 11.1.3 Solving Differential Equations
### 11.1.4 BNF Grammars

> [!note] BNFGrammars
```TLA+ title="BNFGrammars.tla"
---------------------------- MODULE BNFGrammars ----------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences


(* operators for defining sets of tokens *)

\* example: OneOf("abc") = {"a", "b", "c"}
OneOf(s) == {<<s[i]>>: i \in DOMAIN s}
tok(s) == {<<s>>}
Tok(S) == {<<s>>: s \in S}

(* operators for defining languages *)
Nil == {<<>>}
\* concatenations of sentences in L and M
L & M == {s \o t: s \in L, t \in M} 
L | M == L \union M
\* L+
C(L) == 
    LET LL[n \in Nat] == IF n = 0 THEN L ELSE LL[n-1] | LL[n-1] & L
    IN UNION {LL[n]: n \in Nat}
\* L*
CO(L) == Nil | C(L)

L ::= M == L = M
Grammar == [STRING -> SUBSET Seq(STRING)]
LeastGrammar(P(_)) ==
    CHOOSE G \in Grammar:
        /\ P(G)
        /\ \A H \in Grammar: P(H) => \A s \in STRING: G[s] \subseteq H[s]

=============================================================================
```

## 11.2 Other Memory Specifications
### 11.2.1 The Interface
### 11.2.2 The Correctness Condition
### 11.2.3 A Serial Memory
### 11.2.4 A Sequentially Consistent Memory
### 11.2.5 The Memory Specifications Considered


# 12 The Syntactic Analyzer


# 13 The TLATEX Typesetter
## 13.1 Introduction
## 13.2 Comment Shading
## 13.3 How It Typesets the Specification
## 13.4 How It Typesets Comments
## 13.5 Adjusting the Output Format
## 13.6 Output Files
## 13.7 Trouble-Shooting
## 13.8 Using LATEX Commands

# 14 The TLC Model Checker
## 14.1 Introduction to TLC
## 14.2 What TLC Can Cope With
### 14.2.1 TLC Values
### 14.2.2 How TLC Evaluates Expressions
### 14.2.3 Assignment and Replacement
### 14.2.4 Evaluating Temporal Formulas
### 14.2.5 Overriding Modules
### 14.2.6 How TLC Computes States
## 14.3 How TLC Checks Properties
### 14.3.1 Model-Checking Mode
### 14.3.2 Simulation Mode
### 14.3.3 Views and Fingerprints
### 14.3.4 Taking Advantage of Symmetry
### 14.3.5 Limitations of Liveness Checking
## 14.4 The TLC Module


## 14.5 How to Use TLC
### 14.5.1 Running TLC
### 14.5.2 Debugging a Specification
### 14.5.3 Hints on Using TLC Effectively
## 14.6 What TLC Doesn't Do
## 14.7 The Fine Print
### 14.7.1 The Grammar of the Configuration File

### 14.7.2 Comparable TLC Values


# 15 The Syntax of TLA+
## 15.1 The Simple Grammar

> [!note] TLAPlusGrammar
```TLA+ title="TLAPlusGrammar.tla"
--------------------------- MODULE TLAPlusGrammar ---------------------------
EXTENDS Natruals, Sequences, BNFGrammars

CommaList(L) == L & CO(tok(",") & L)
AtLeast4(s) == Tok({s \o s \o s} & C({s}))

ReservedWord == {"ASSUME", "ELSE", "LOCAL", "UNION",
"ASSUMPTION", "ENABLED", "MODULE", "VARIABLE",
"AXIOM", "EXCEPT", "OTHER", "VARIABLES",
"CASE", "EXTENDS", "SF_", "WF_",
"CHOOSE", "IF", "SUBSET", "WITH",
"CONSTANT", "IN", "THEN",
"CONSTANTS", "INSTANCE", "THEOREM",
"DOMAIN", "LET", "UNCHANGED"}

Letter == OneOf("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")
Numeral == OneOf("0123456789")
NameChar == Letter \union Numeral \union {"-"}

Name == Tok( CO(NameChar) & Letter & CO(NameChar) \ ({"WF_", "SF_"} & C(NameChar)))
Identifier == Name \ Tok(ReservedWord)

IdentifierOrTuple == Identifier | tok("<<") & CommaList(Identifier) & tok(">>")

NumberLexeme == C(Numeral)
    | (CO(Numeral) & {"."} & C(Numeral))
    | {"\\b", "\\B"} & C(OneOf("01"))
    | {"\\o", "\\O"} & C(OneOf("01234567"))
    | {"\\h", "\\H"} & C(OneOf("0123456789abcdefABCDEF"))

Number == Tok(NumberLexeme)

String == Tok({"\"" & STRING & {"\""}})

=============================================================================
```

## 15.2 The Complete Grammar
### 15.2.1 Precedence and Associativity
### 15.2.2 Alignment
### 15.2.3 Comments
### 15.2.4 Temporal Formulas
### 15.2.5 Two Anomalies
## 15.3 The Lexemes of TLA+


# 16 The Operators of TLA+
## 16.1 Constant Operators
### 16.1.1 Boolean Operators
### 16.1.2 The Choose Operator
### 16.1.3 Interpretations of Boolean Operators
### 16.1.4 Conditional Constructs
### 16.1.5 The Let/In Construct
### 16.1.6 The Operators of Set Theory
### 16.1.7 Functions
### 16.1.8 Records
### 16.1.9 Tuples
### 16.1.10 Strings
### 16.1.11 Numbers


## 16.2 Nonconstant Operators
### 16.2.1 Basic Constant Expressions
### 16.2.2 The Meaning of a State Function
### 16.2.3 Action Operators
### 16.2.4 Temporal Operators

# 17 The Meaning of a Module
## 17.1 Operators and Expressions
### 17.1.1 The Arity and Order of an Operator
### 17.1.2 $\lambda$ Expressions
### 17.1.3 Simplifying Operator Application
### 17.1.4 Expressions
## 17.2 Levels
## 17.3 Contexts
## 17.4 The Meaning of a $\lambda$ Expression
## 17.5 The Meaning of a Module
### 17.5.1 Extends
### 17.5.2 Declarations
### 17.5.3 Operator Definitions
### 17.5.4 Function Definitions
### 17.5.5 Instantiation
### 17.5.6 Theorems and Assumptions
### 17.5.7 Submodules
## 17.6 Correctness of a Module
## 17.7 Finding Modules
## 17.8 The Semantics of Instantiation


# 18 The Standard Modules

# Summary

Summary of TLA+
## Module-Level Constructors
```TLA+
-------- MODULE M --------
EXTENDS M1, ..., Mn
CONSTANTS C1, ..., Cn
VARIABLES x1, ..., xn
ASSUME P
F(x1, ..., xn) == exp
f[x \in S] == exp
INSTANCE M WITH p1 <- e1, ..., pm <- em
N(x1, ..., xn) == INSTANCE M WITH p1 <- e1, ..., pm <- em
THEOREM P
LOCAL def
----------------
```
## The Constant Operators
Logic
```TLA+ title="Logic"
/\
\/
~ \lnot \neg
=>
<=> \equiv
TRUE
FALSE
BOOLEAN {TRUE, FALSE}
\A x \in S: p
\E x \in S: p
CHOOSE x \in S: p 
```
Sets
```TLA+ title="Sets"
=
# /=
\in
\notin
\cup \union
\cap \intersect
\subseteq
\
{e1, ..., en}
{x \in S: p}
{e: x \in S}
SUBSET S
UNION S
```
Functions
```TLA+ title="Functions"
f[e]
DOMAIN f
[x \in S |-> e]
[S -> T]
[f EXCEPT 
	![e1] = e2]
```
Records
```TLA+ title="Records"
e.h
[h1 |-> e1, ..., hn |-> en]
[h1: S1, ..., hn: Sn]
[r EXCEPT 
	!.h = e]
```
Tuples
```TLA+ title="Tuples"
e[i]
<<e1, ..., en>>
S1 \X ... \X Sn
```
Strings and Numbers
```TLA+ title="Strings and Numbers"
"c1 ... cn"
STRING
<<e1, ..., en>>
d1...dn d1...dn.d_n+1...dm
```

## Miscellaneous Constructs
```TLA+ title=""
IF p THEN e1 ELSE e2
CASE p1 -> e1 [] ... [] pn -> en
CASE p1 -> e1 [] ... [] pn -> en [] OTHER -> e
LET d1 == e1 ... dn == en IN e

/\ p1
   ...
/\ pn

\/ p1
   ...
\/ pn
```

## Action Operators
```TLA+ title=""
e'
[A]_e
<<A>>_e
ENABLED A
UNCHANGED e
A \cdot B
```

## Temporal Operators
```TLA+ title=""
[]F
<>F
WF_e(A)
SF_e(A)
F ~> G
```

## User-Definable Operator Symbols
Infix Operators
```TLA+ title="Infix Operators"
+ - * / \o \circ ++
\div % ^ .. ... --
(+) \oplus (-) \ominus (\X) \otimes (/) \oslash (.) \odot **
< > <= =< \leq >= \geq \sqcap //
\prec \succ \preceq \succeq \sqcup ^^
\ll \gg <: :> & &&
\sqsubset \sqsupset \sqsubseteq \sqsupseteq | %%
\subset \supset \subseteq \supseteq \star @@
|- -| |= =| \bullet ##
\sim \simeq \approx  \cong $ $$
\bigcirc ::= \asymp \doteq ?? !!
\propto \wr \uplus
```
Postfix Operators
```TLA+ title="Postfix Operators"
^+ ^* ^#
```

## Precedence Ranges of Operators
```TLA+ title=""

```

## Operators Defined in Standard Modules
Naturals, Integers, Reals
```TLA+ title="Naturals, Integers, Reals"
+
- 
*
/
^
..
Nat
Real
\div
%
\leq =< <=
\geq >=
<
>
Int
Infinity
```
Sequences
```TLA+ title="Sequences"
\o \circ
Head
SelectSeq
SubSeq
Append
Len
Seq
Tail
```
FiniteSets
```TLA+ title="FiniteSets"
IsFiniteSet
Cardinality
```
Bags
```TLA+ title="Bags"
(+) \oplus
BagIn
CopiesIn
SubBag
(-) \ominus
BagOfAll
EmptyBag
\sqsubseteq
BagToSet
IsABag
BagCardinality
BagUnion
SetToBag
```
RealTime
```TLA+ title="RealTime"
RTBound
RTnow
now
```
TLC
```TLA+ title="TLC"
:>
@@
Print
Assert
JavaTime
Permutations
SortSeq
```
