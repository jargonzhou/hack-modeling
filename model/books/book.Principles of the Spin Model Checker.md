# Principles of the Spin Model Checker


# 1 Sequential Programming in PROMELA
SPIN is a model checker - a software tool for verifying models of physical system, in particular, computerized systems.

PROMELA is a language that is used for writing models in SPIN.

## 1.1 A first program in PROMELA

Assignment statements and expression in PROMELA are written using the syntax of C-like lanauage.
Programs in PROMELA are composed of a set of **processes** (`active proctype`), processes my ave parameters.
The statements of the process are written between the braces `{` and `}`.
Commemts are enclosed between `/*` and `*/`. There is also a single line comments: `//`.

> [!example] "Reversing digits" 

```promela title="reversing_digits.pml" linenums="1"
active proctype P() {
  int value = 123; /* Try with a byte variable here ... */
  int reversed; /* ... and here! */
  reversed =
    (value % 10) * 100 +
    ((value / 10) % 10) * 10 +
    (value / 100);
  printf("value = %d, reversed = %d\n", value, reversed)
}
```

- `value`, `reversed`: two variables of type `int`
- `printf`: a statement taken from the C language

## 1.2 Random simulation

In simulation mode, SPIN compiles and executes a PROMELA program.

By convention, we use the extension `pml` for PROMELA files.

To run a random simulation:

- jSpin: after load a file or create a new file, select `Check` to perform a syntax check, select `Random` to compile and execute the program. 
- command line: `spin filename`.

Set a limit on the number of steps that will be executed in a simulation run:

- jSpin: select `Setting/Max steps` and enter a value.
- command line: `spin -uN`, `N` is the maximum number of steps.

Input in PROMELA:

- By convention, a PROMELA program does not have input, since it is intended for simulating a closed system.
- There is an input channel `STDIN` connected to standard input that can be useful for running simulations of a single model with different parameters.

## 1.3 Data types

The numeric data types of PROMELA are based upon those of the C compiler used to compile SPIN itself.
All effort should be made to mode ldata using tyoes that need as few bits as possible to avoid combinatorial explosion in the number of states during a verification.

??? note "Numeric data types in PROMELA"

```
Type        Values            Size(bits)
bit,bool    0,1,false,true    1
byte        0..255            8
short       -32768..32767     16
int         -2^31..2^31-1     32
unsigned    0..2^n-1          <= 32
```

There are no character type, string type, or floating-point type in PROMELA.

The recommendation to give explicit initial values can affect the size of models in SPIN.
The type `unsigned` is meaningful when compression of the state vector is used.

### 1.3.1 Type conversions

There are no explicit type conversions in PROMELA.
Arithmetic is always performed by first implicitly converting all values to `int`;
upon assignment, the value is implicitly converted to the type of the variable.

SPIN leaves it up to you to decide if the truncated value is meaningful or not.

## 1.4 Operators and expressions

Expression in PROMELA **must be side-effect free**.
The reason for this is that expressons are used to determine if a statement is executable or not.

??? note "Operators in PROMELA"

```
Precedence Operator        Associativity Name
14         ()              left          parentheses
14         []              left          array indexing
14         .               left          field selection
13         !               right         logical negation
13         ~               right         bitwise complementation
13         ++, --          right         increment, decrement
12         *, /, %         left          multiplication, division, modulo
11         +, -            left          addition, subtraction
10         <<, >>          left          left and right bitwise shift
9          <, <=, >, >=    left          arithmetic relational operators
8          ==, !=          left          equality, inequality
7          &               left          bitwise and
6          ^               left          bitwise exclusive or
5          |               left          bitwise inclusive or
4          &&              left          logical and
3          ||              left          logical or
2          ( -> : )        right         conditional expression
1          =               right         assignment
```

The difference between PROMELA and the C language, in PROMELA:

- Assignment statements are not expressions.
- The increment and decrement operators (`++`, `--`) may only be used as postfix operators in an assignment statement (like `b++`) and not in an expression like the right-hand side of an assignment statement (like `a = b++`).
- There are no prefix increment and decrement operators.

### 1.4.1 Local variables

The scope of a local variable is the entire process in which it is declared.
It is not necessary to declare variables at the beginning of a process; 
however, all variable declarations are implicitly moved to the beginning of the process.

> [!example] "Variable Declaration"

```promela title="var-decl.pml"
byte a = 1;
// . . .
a = 5;
byte b = a+2;
printf("b= %d\n", b);
```

- The output is 3: the variable `b` is implicitly declared immediately after the declaration of `a`.

### 1.4.2 Symbolic names

A preprocessor macro can be used at the beginning of the program to declare a symbol for a number, and textual substitution is used when the symbol is encountered:

> [!example] "`#define`"

```promela
#define N 10

i = j % N;
```

The type `mtype` can be used to give mnemonic names to values.
The symbolic values can be printed using the `%e` format specifier, and they will appear in the traces of programs. 
The `printm` statement can be used to print a value of an `mtype`.
Internally, the values of the `mtype` are represented as positive byte values.
A limitation on `mtype` is that there is only one set of names defined for an entire program.

> [!example] "`mtype`"

```promela
mtype = { red, yellow, green };
mtype light = green;

active proctype P() {
    do
    :: if
       :: light == red -> light = green
       :: light == yellow -> light = red
       :: light == green -> light = yellow
       fi;
       printf("The light is now %e\n", light)
    od
}
```

Adding new symbolic names:

```promela title="symbolic-names.pml"
mtype = { red, yellow, green };
mtype = { green_and_yellow, yellow_and_red };
mtype light = green;

active proctype P() {
    do
    :: if
       :: light == red -> light = yellow_and_red
       :: light == yellow_and_red -> light = green
       :: light == green -> light = green_and_yellow
       :: light == green_and_yellow -> light = red
       fi;
       printf("The light is now %e\n", light)
    od
}
```

## 1.5 Control statements

The control statements are taken from a formalism called **guarded commands** invented by E.W. Dijkstra.
This formalism is particularly well suited for expressing nondeterminism.

There are 5 control statements:

- sequence
- selection
- repetition
- jump
- `unless`

The semicolon `;` is the seperator between statements that are executed in sequence.

??? note "Location Counter, Control Point"

When a processor executes a program, a register called a **location counter** maintains the address of the next instruction that can be executed.

An address of an instruction is called a **control point**.

example:

```promela
x = y + 2;
z = x * y;
printf("x = %d, z = %d", x , z)
```

has 3 control points, one before each statement, and the location counter of a process can be at any one of them.

## 1.6 Selection statements

> [!example] "`if`-statement in Java or C"

```C
if (expression1) {
    statement11; statement12; statement13;
}
else if (expression2) {
    statement21;
}
else {
    statement31; statement32;
}
```

In SPIN there is no semantic meaning to the order of the alternatives,
the semantics of the statement merely says that is the expression of an alternative is true, the sequence of statements that follow it can be executed.

> [!example] "`if`-statement"

discriminant of a quadratic equaltion:

```promela title="ifs.pml"
active proctype P() {
  int a = 1, b = -4, c = 4;
  int disc;
  disc = b * b - 4 * a * c;
  if
  :: disc < 0 ->
    printf("disc = %d: no real roots\n", disc)
  :: disc == 0 ->
    printf("disc = %d: duplicate real roots\n", disc)
  :: disc > 0 ->
    printf("disc = %d: two real roots\n", disc)
  fi
}
```

- the three expression are mutually exclusive and exhaustive: exactly one of them will be true whenever the statement is executed.

An `if`-statement starts with the reserved word `if` and ends with the reserved word `fi`.
In between are one or more **alternatives**, each consisting of a double colon `::`, a statement called a **guard**, an arrow `->` and a sequence of statements.
The arrow symbol `->` is a syntactic sugar for a semicolon `;`. Gaurds are simple PROMELA statements with no special syntax.

The execution of an `if`-statement begins with the evaluation of the guards;
if at least one evaluates to true, the sequence of statements following the arrow corresponding to one of the true guards is executed.
When those statements have been executed, the `if`-statement terminates.

The `else` guard: if and only if all the other guards evaluate to false, the statements following the `else` will be executed.

When all alternatives are false, the process **blocks** until some guard evaluates to true, which can only happen in a concurrent program with more than one process.

The sequence of statements following a guard can be empty, in which case control leaves the `if`-statement after evaluating the guard.
We can also use `skip`, which is a syntactic sugar for a statement that always evaluates to true like `true` or `(1)`.

??? note "Random Simulation"

Whenever a nondeterministic choice exists, SPIN randomly chhooses one of them.

In `if`-statements, if two or more guards evaluate to true, the statements associated with either may be executed.

> [!example] "More `if`-statements"

Number of days in a month:

```promela
active proctype P() {
  byte days;
  byte month = 2;
  int year = 2000;
  if
  :: month == 1 || month == 3 || month == 5 ||
    month == 7 || month == 8 || month == 10 ||
    month == 12 ->
      days = 31
  :: month == 4 || month == 6 || month == 9 ||
    month == 11 ->
      days = 30
  :: month == 2 && year % 4 == 0 && /* Leap year */
    (year % 100 != 0 || year % 400 == 0) ->
      days = 29
  :: else ->
      days = 28
  fi;
  printf("month = %d, year = %d, days = %d\n",
    month, year, days)
}
```

Maximum of two values:

```promela title="max.pml"
active proctype P() {
  int a = 5, b = 5;
  int max;
  int branch;
  if
  :: a >= b -> max = a; branch = 1
  :: b >= a -> max = b; branch = 2
  fi;
  printf("The maximum of %d and %d = %d by branch %d\n",
    a, b, max, branch)
}
```

### 1.6.1 Conditional expressions

A conditional expression enables we to obtain a value that depends on the result of evaluating a boolean expreson, for example: `max = (a > b -> a : b)`, this assignment is an atomic statement.

A conditional expression must be contained within parentheses.

> [!example] "Conditional Expressions"

```promela
:: month == 2 && year % 4 == 0 ->
    days = (year % 100 != 0 || year % 400 == 0 -> 29 : 28)
```

The semantics of conditional expressions is different from that of `if`-statement.

An assignment statement like `max = (a > b -> a : b)` is an atomic statement, while the `if`-statement

```promela
if
:: a > b -> max = a
:: else  -> max = b
fi
```

is not, and interleaving is possible between the guard and the following assignment statement.

## 1.7 Repetitive statements

`do`-statement is the repetitive statement in PROMELA.

The semantics of `do`-statement is similar to the `if`-statement, consisting of the evaluation of the guards, followed by the execution of the sequence of statements following one of the true guards.

For a `do`-statement, completion of the sequence of statement causes the execution to return to the beginning of the `do`-statement and the evaluation of the guards is begun again.

Termination of a loop is accomplished by `break`, which is not a statement but rather an indication that control passes from the current location to the statement following the `od`.

> [!example] "`do`-statement"

Greatest common denominator:

```promela title="dos.pml"
active proctype P() {
  int x = 15, y = 20;
  int a = x, b = y;
  do
  :: a > b -> a = a - b
  :: b > a -> b = b - a
  :: a == b -> break
  od;
  printf("The GCD of %d and %d = %d\n", x, y, a)
}
```

### 1.7.1 Counting loops

There are no counting loops in PROMELA similar to the `for`-statement of C-like language.

> [!example] "A couting loop"

```promela
#define N 10

active proctype P() {
  int sum = 0;
  byte i = 1;
  do
  :: i > N -> break
  :: else ->
    sum = sum + i;
    i++
  od;
  printf("The sum of the first %d numbers = %d\n", N, sum)
}
```

Use the `for` macro:

```promela title="for-loop2.pml"
#include "for.h"
#define N 10

active proctype P() {
  int sum = 0;
  for (i, 1, N)
    sum = sum + i
  rof (i);
  printf("The sum of the first %d numbers = %d\n", N, sum)
}
```

- The `for` macro takes 3 parameters: the control variable, the lower and upper limits of the loop.
- The `rof` macro at the end of the loop takes the control variable as a parameter.
- The text of these macros is contained in `for.h`.

## 1.8 Jump statements

PROMELA contains a `goto`-statement taht causes control to jump to a label, which is an identifier followed by a colon `:`.

> [!example] "`goto`-statement"

`goto` can be used instead of `break` to exit a loop:

```promela
do
:: i > N -> goto exitloop
:: else -> ...
od;
exitloop:
  printf(...);
```

attach a label to the entire `do`-statement:

```promela
start:
  do
  :: wantP ->
    if
    :: wantQ -> goto start
    :: else -> skip
    fi
  :: else ->
    ...
  od
```

??? note "Joint Control Point"

There is no control point at the beginning of an alternative in an `if`- or `do`-statement, so it is a syntax error to place a label in front of a guard.

Instead, there is a **joint control point** for all alternatives at the beginning of the statement.


# 2 Verification of Sequential Programs
## 2.1 Assertions

A **state** of a program is a set of values of its variables and location counters.
A **computation** of a program is a sequence of states beginning with an initial state and continuing with the states that occur as each statement is executed.

> [!example] "State, Computation"

```promela title="reversing_digits.pml" linenums="1"
active proctype P() {
  int value = 123; /* Try with a byte variable here ... */
  int reversed; /* ... and here! */
  reversed =
    (value % 10) * 100 +
    ((value / 10) % 10) * 10 +
    (value / 100);
  printf("value = %d, reversed = %d\n", value, reversed)
}
```

- A state of this program is a triple, such as `(123, 321, 8)`, where the first element `123` is the value of the variable `value`, the second element `321` is the value of `reversed`, the third `8` is the location counter.
- The only one compucation for this program is `(123, 0, 4) -> (123, 321, 8) -> (123, 321, 9)`.

The **state space** of a program is the set of states that can *possibly* occur during a computation.
In model checking, the state space of a program is generated in order to search for a counterexample - if one exists - to the correctness specifications.

**Assertions** can be used to express correctness specifications.
Assertions can be placed between any two statements of a program and the model checker will evaluate the assertions as part of its search of the state space.
If, during the search, it finds a computation leading to a false assertion, either the program is incorrect, or the assertion does not properly express a correctness property that holds for the program.

Assertions are statements consiting of the keyword `assert` followd by an expression.
When an `assert` statement is executed during a simulation, the expression is evaluated.
If it is true, execution proceeds normally to the next statement; if it is false, the program terminates with an error message.

> [!example] "`assert`"

Integer division:

```promela title="divide.pml" linenums="1" hl_lines="6 20 21"
active proctype P() {
  int dividend = 15;
  int divisor = 4;
  int quotient, remainder;

  assert (dividend >= 0 && divisor > 0);

  quotient = 0;
  remainder = dividend;
  do
  :: remainder >= divisor ->
    quotient++;
    remainder = remainder - divisor
  :: else ->
    break
  od;
  printf("%d divided by %d = %d, remainder = %d\n",
    dividend, divisor, quotient, remainder);

  assert (0 <= remainder && remainder < divisor);
  assert (dividend == quotient * divisor + remainder)
}
```

- The assertion in line 6 is the **precondtion**: an assertion that specifies waht must be true in the initial state.
- The assertions in line 20 and 21 are the **postconditions**: assertions that specify what must be true in any final state of the program.

Run a random simulation:

```shell
15 divided by 4 = 3, remainder = 3
```

```promela title="divide-error.pml" linenums="1" hl_lines="2 11"
active proctype P() {
  int dividend = 16;
  int divisor = 4;
  int quotient, remainder;

  assert (dividend >= 0 && divisor > 0);

  quotient = 0;
  remainder = dividend;
  do
  :: remainder > divisor ->
    quotient++;
    remainder = remainder - divisor
  :: else ->
    break
  od;
  printf("%d divided by %d = %d, remainder = %d\n",
    dividend, divisor, quotient, remainder);

  assert (0 <= remainder && remainder < divisor);
  assert (dividend == quotient * divisor + remainder)
}
```

Run a random simulation:

```shell
spin: line 20 "divide-error.pml", Error: assertion violated
spin: text of failed assertion:
    assert(((0<=remainder)&&(remainder<divisor)))
```

Another program for integer division:

```promela linenums="1" hl_lines="11 12"
active proctype P() {
  int dividend = 15, divisor = 4;
  int quotient = 0, remainder = 0;
  int n = dividend;

  assert (dividend >= 0 && divisor > 0);

  do
  :: n != 0 ->

    assert (dividend == quotient * divisor + remainder + n);
    assert (0 <= remainder && remainder < divisor);

    if
    :: remainder + 1 == divisor ->
      quotient++;
      remainder = 0
    :: else ->
      remainder++
    fi;
    n--
  :: else ->
    break
  od;
  printf("%d divided by %d = %d, remainder = %d\n",
    dividend, divisor, quotient, remainder);

  assert (0 <= remainder && remainder < divisor);
  assert (dividend == quotient * divisor + remainder)
}
```

- The assertions in line 11 and 12 are the **invariants** of the loop: an assertion within a loop which must reamin true as long as the loop body continues to be executed.

??? note "Deductive verification"

An alternative approach to verification is **deduction**.
A formal semantics is defined for program constructs and then a formal logic with axioms and inference rules is used to deduce that a program satisfies correctness specifications, expressed, for example, as assertions.

The advantage of deductive verification is that it is not limited by the size of the state space because the deduction is done on symbolic formulas;
the disadvantage is taht it is less amenable to automation and requires mathematical ingenuity.

A textbook: Krzysztof R. Apt and Ernst-Rüdiger Olderog. **Verification of Sequential and Concurrent Programs**. Springer, Berlin, 1991.


## 2.2 Verifying a program in SPIN

The only way to verify that a program is correct is to systematically check that the correctness specifications hold in **all possible computations**.

Verification in SPIN is a three-step process:

- Generate the verifier from the PROMELA source code. The verifier is a program written in C.
- Compile the verifier using a C compiler.
- Execute the verifier. The result of the execution of the verifier is a report that all computations are correct or else that some computation contains an error. There is also an tail can be used to reconstruct a compuation that leads to an error.

To run a verification:

- jSpin: select `Verify`.
- command line: `spin -a max.pml`, `gcc -o pan pan.c`, `pan`.

SPIN stops as soon as one assertion is violated, we can use argument `-e` to `pan` to create tails for all errors. and argument `-cN` to stop at the Nth error rather then the first.

> [!example] "Maximum with an error"

```promela title="max-error.pml" linenums="1" hl_lines="5"
active proctype P() {
  int a = 5, b = 5, max;
  if
  :: a >= b -> max = a;
  :: b >= a -> max = b+1;
  fi;
  assert (a >= b -> max == a : max == b)
}
```

- When `a` equals `b`, a random simulation is just as likely to take the first alternative of the `if`-statement as the second.
- Even if we run the simulation repeatedly, it is possible that the same alternative will always be taken.

Run a verification:

```shell
pan: assertion violated
    ( ((a>=b)) ? ((max==a)) : ((max==b)) ) (at depth 0)
pan: wrote max1.pml.trail
(Spin Version 4.2.8 6 January 2007)
Warning: Search not completed
    ...
Statevector 24 byte, depth reached 2, errors: 1
    ...
```

### 2.2.1 Guided simulation

SPIN supports the analysis of failed verifications by maintaining internal data structures during its search of the state space; these are used to reconstruc a computation that leads to an error.
The data required for reconstructing a computation are written into a file called a **trail** (`*.trail`).
The trail file is used to reconstruct a computation by running SPIN in **guided simulation mode**.

To run SPIN in guided simulation mode:

- jSpin: after running a verification that has reported errors, select `Trail`.
- command line: after running a verification that has reported errors, run `spin -t max.pml`.

> [!example] "Maximum with an error"

Run a guided simulation:

```shell
Starting P with pid 0
  0: proc - (:root:) creates proc 0 (P)
0 P  3 b>=a
0 P  5 max = (b+1)
```

- The bad compuation occurs when the alternative the mistake (in line 5) is executed.

### 2.2.2 Displaying a computation

SPIN can print these data in a computation produced by random or guided simulation:

- The statements executed by the processes.
- The values of the global variables.
- The values of the local variables.
- Send instructions executed on a channel.
- Receive instructions executed on a channel.

To select data to display:

- jSpin: select `Options/Common`.
- command line: `-p` for statements, `-g` for globals, `-l` for locals, `-s` for send, `-r` for receive.


# 3 Concurrency
SPIN supports modeling of both concurrent and distributed systems.

## 3.1 Interleaving

> [!example] "Interleaving statements"

```promela linenums="1" title="interleaving.pml"
byte n = 0;

active proctype P() {
  n = 1;
  printf("Process P, n = %d\n", n)
}

active proctype Q() {
  n = 2;
  printf("Process Q, n = %d\n", n)
}
```

One computation of the program:

```shell
Process   Statement     n     Output
P         n = 1         0
P         printf(P)     1
Q         n = 2         1     P, n = 1
Q         printf(Q)     2
                              Q, n = 2
```

All possible computations of the program:

```shell
n = 1     n = 1     n = 1     n = 2     n = 2     n = 2
printf(P) n = 2     n = 2     printf(Q) n = 1     n = 1
n = 2     printf(P) printf(Q) n = 1     printf(Q) printf(P)
printf(Q) printf(Q) printf(P) printf(P) printf(P) printf(Q)
```

We say that the compuations of a program are obtained by **arbitrarily interleaving** of the statements of the processes.
If each process $p_{i}$ were run by iteself, a computation of the process would be a sequence of states $(s_{i}^{0}, s_{i}^{1}, s_{i}^{2}, \cdots)$, where state $s_{i}^{j+1}$ follows state $s_{i}^{j}$ if and only if it is obtained by executing the statement at the location counter of $p_{i}$ in $s_{i}^{j}$.

The computation obtained by running all processes concurrently is a sequence of states $(s^{0}, s^{1}, s^{2}, \cdots)$, where $s^{j+1}$ follows state $s^{j}$ if and only if it is obtained by executing the statement at the location counter of some process in $s^{j}$.

The word **interleaving** is intended to represent this image of **selecting** a statement from the possible computations of the individual processes and **merging** them into a computation of all the processes of the system.

### 3.1.1 Displaying a computation

When SPIN simulates a program, it create one computation by interleaving the statements of all the processes.
SPIN writes a description of the computation on standard output.

> [!example] "Displaying a computation"

jSpin:

```shell
// output Process Q, n = 2
Process P, n = 1
2 processes created

// tabular format
Process     Statement             n
0 P         4 n = 1
0 P         5 printf(’Proces      1
1 Q         9 n = 2 1
1 Q         10 printf(’Proces     2
```

command line:

```shell
// computation 4
        Process Q, n = 2
    Process P, n = 1
2 processes created

// computation 6
    Process P, n = 1
        Process Q, n = 1
2 processes created

// -p -g
Starting P with pid 0
0: proc  - (:root:) creates proc 0 (P)
Starting Q with pid 1
0: proc  - (:root:) creates proc 1 (Q)
1: proc  1 (Q) line 9 (state 1) [n = 2]
            n = 2
    Process Q, n = 2
2: proc  1 (Q) line 10 (state 2) [printf(Q)]
2: proc  1 (Q) terminates
3: proc  0 (P) line 4 (state 1) [n = 1]
            n = 1
    Process P, n = 1
4: proc  0 (P) line 5 (state 2) [printf(Q)]
4: proc  0 (P) terminates
2 processes created
```

## 3.2 Atomicity

Statements in PROMELA are **atomic**.
At each step, the statement pointed to by the location counter of some arbitrary process is executed in its entirety.

Expressions in PROMELA are statements.
In an `if`- or `do`-statement it is possible for interleaving to occur between the evaluation of the expression (statement) that is the guard and the execution of the statement after the guard.

> [!example] "Interleaving in `if`- or `do`-statement"

`a` is a global variable.

```promela
if
:: a != 0 ->
    c = b / a
:: else ->
    c = b
fi
```

We cannot infer that division by zero is impossible.
Between the evaluation of the guard `a != 0` and the execution of the assignment statement `c = b / a`, 
some other process might have assigned zero to `a`.

## 3.3 Interactive simulation

With **interactive simulation**, a specific compuation can be constructed.
Before each step that has a **choice point** , either because of nondeterminism within a single process or when a choice of the next statement to execute can be made from several processes, we are presented with the various choices and can interactively choose which one to execute.

To run an interactive simulation:

- jSpin: select `Interactive`.
- command line: use the argument `-i`.

## 3.4 Interference between processes

> [!example] "Interference between two processes"

```promela linenums="1" title="interference.pml"
byte n = 0;

active proctype P() {
  byte temp;
  temp = n + 1;
  n = temp;
  printf("Process P, n = %d\n", n)
}

active proctype Q() {
  byte temp;
  temp = n + 1;
  n = temp;
  printf("Process Q, n = %d\n", n)
}
```

- Between the statements of process P on lines 5 and 6, it is possible to interleave statements from process Q, and similarly for process Q.
- Such interleaving would not be possible if the computation were performed in a single atomic statement `n = n + 1`.

Perfect interleaving: both copy the same initial value, and the updated value from one process is overwritten by the updated value from the second process.

```shell
Process Statement     n P:temp Q:temp Output
P       temp = n + 1  0 0      0
Q       temp = n + 1  0 1      0
P       n = temp      0 1      1
Q       n = temp      1 1      1
P       printf(P)     1 1      1
Q       printf(Q)     1 1      1      P, n = 1
                                      Q, n = 1
```

## 3.5 Sets of processes

Instead of writing them separately, a set of identical processes can be declared.
The number in brackets following the keyword `active` indicates the number of processes to instantiate.

> [!example] "Instantiating two processes"

```promela title="processes.pml"
byte n = 0;

active [2] proctype P() {
  byte temp;
  temp = n + 1;
  n = temp;
  printf("Process P%d, n = %d\n", _pid, n)
}
```

There are two ways to distinguish between the processes:

- use the predefined variable `_pid`, which is of a seperate type `pid` but actually similar to `byte`. Each time that a process is instantiated, it is assigned a **process identifier** starting with zero.
- use the `run` operator. The keyword `run` is followed by the name oa a **process type**, which is indicated by `proctype` without the keyword `active`; this causes a process of that type to be instantiated. `run` is used to supply intial values to a process: the formal parameters are declared in the process type and are local variables initialized with the values of the actual parameters.

The formal parameters of a `proctype` are separated with semicolons `;`, not commas `,`.

Processes in PROMELA are usually instantiated in a process called `init`, which - if it exists - is always the first process activated and thus the value of `_pid` in this process is 0.

By convention, `run` statements are enclosed in an `atomic` sequence to ensure that all processes are instantiated before any of them begins execution.

`run` is an operator, so `run P()` is an expression, not a statement, and it returns a value: the process ID of the process that is instantiated, or zero if the maximum number of processes (255) have already been instantiated.

> [!example] "`run`, `init`"

```promela title="run-init.pml" linenums="1"
byte n;

proctype P(byte id; byte incr) {
  byte temp;
  temp = n + incr;
  n = temp;
  printf("Process P%d, n = %d\n", id, n)
}

init {
  n = 0;
  atomic {
    run P(1, 10);
    run P(2, 15)
  }
}
```

- The processes are instantiated in an `init` process, where they are passed an explicit identifier `id`, as well as an additional value `incr` that is used in the assignment statements.
- The initialization of the global variable has also been moved to the `init` process, though this would normally be done only for non-trivial initialization code sunch as the nondeterministic selection of a value.

## 3.6 Interference revisited

> [!example] "Counting with interference"

The use of `init` enables us to write a fascinating program for demonstrating interference.

There are two processes, each of which increments the global variable `n` ten times: 

```promela title="interference2.pml" linenums="1"
#include "for.h"
byte n = 0;

proctype P() {
  byte temp;
  for (i, 1, 10)
    temp = n + 1;
    n = temp
  rof (i)
}

init {
  atomic {
    run P();
    run P()
  }
  (_nr_pr == 1) ->
    printf("The value is %d\n", n)
}
```

- `_nr_pr`: a predefined variable whose value is the number of processes currently active. `(_nr_pr == 1)` causes process `init` to be blocked until the expression evaluates to true, which occurs only the process `init` itself.

computations:

- (1) without interference: one process executes all its statements in sequence, the final value of `n` is 20.
- (2) with perfect interleaving: alternately selecting one statement from each process, the final value is 10. 

```shell
Process Statement     n P:temp Q:temp Output
P       temp = n + 1  0 0      0
Q       temp = n + 1  0 1      0
P       n = temp      0 1      1
Q       n = temp      1 1      1
P       printf(P)     1 1      1
Q       printf(Q)     1 1      1      P, n = 1
                                      Q, n = 1
```

- (3) the final value is 2. (verification can be used to discover it.)

## 3.7 Deterministic sequences of statements

There are two ways of creating **atomic sequences of statements**:

- `d_step`: deterministic step.
- `atomic`.

> [!example] "Deterministic step"

```promela title="d_steps.pml" linenums="1" hl_lines="5 14"
byte n = 0;

active proctype P() {
  byte temp;
  d_step {
    temp = n + 1;
    n = temp
  }
  printf("Process P, n = %d\n", n)
}

active proctype Q() {
  byte temp;
  d_step {
    temp = n + 1;
    n = temp
  }
  printf("Process Q, n = %d\n", n)
}
```

computation:

```shell
Process Statement                 n P:temp Q:temp Output
P       temp = n + 1; n = temp    0 0      0
Q       temp = n + 1; n = temp    1 1      0
P       printf("P")               2 1      2
Q       printf("Q")               2 1      2      P, n = 2
                                                  Q, n = 2
```

There are many synchronization primitives such as *test-and-set* and `exchange` that are based upon the atomic execution of a sequence of statements. Implementations in PROMELA are given in the software archive for PCDP.

## 3.8 Verification with assertions

To get the computation (3) in example *Counting with interference*, we can add the assertion `assert (n > 2)` at the end of the program and running a verification.
What SPIN does is to search the state space looking for **counterexamples**, that is, computations that are in error.

Run a verification:

```shell
pan: assertion violated (n>2) (at depth 89)
```

## 3.9 The critical section problem

> [!example] "Incorrect solution for the critical section problem"

```promela linenums="1"
bool wantP = false, wantQ = false;

active proctype P() {
  do
  :: printf("Noncritical section P\n");
    wantP = true;
    printf("Critical section P\n");
    wantP = false
  od
}

active proctype Q() {
  do
  :: printf("Noncritical section Q\n");
    wantQ = true;
    printf("Critical section Q\n");
    wantQ = false
  od
}
```

- Each process executes a nonterminating `do`-statement (lines 4-9, 13-18), alternating between the critical and the noncritical sections which are represented by `printf` statements.
- The possibility of halting in the noncritical section has not been modeled.

> [!example] "Verifying mutual exclusion"

```promela title="cs.pml" linenums="1" hl_lines="8 11 20 23"
bool wantP = false, wantQ = false;
byte critical = 0;

active proctype P() {
  do
  :: printf("Noncritical section P\n");
    wantP = true;
    critical++;
    printf("Critical section P\n");
    assert (critical <= 1);
    critical--;
    wantP = false
  od
}

active proctype Q() {
  do
  :: printf("Noncritical section Q\n");
    wantQ = true;
    critical++;
    printf("Critical section Q\n");
    assert (critical <= 1);
    critical--;
    wantQ = false
  od
}
```

- In a conccurent program, we generally need correctness specifications that consider the global state of all the processes in the program.
- To specify that two processes cannot be in their critical sections at the same time, we introduce a new variable `critical` that is not part of the algorithm but is only used for verification. Such a variable is called a **ghost variable**. The variable is incremented before executing a critical section (line 8, 20) and decremented afterwards (line 11, 23).
    
```shell
spin: line 23 "cs.pml", Error: assertion violated
spin: text of failed assertion: assert((critical<=1))
#processes: 2
Process Statement     critical wantP wantQ
1 Q                   2        1     1
0 P                   2        1     1
```

We need synchronization between processes in order to solve the critical section problem.


# 4 Synchronization
PROMELA does not have synchronization primitives such as semaphores, locks, and monitors that we may have encountered.
Instead, we model primitives by building on the concept of the **executability** of statements.

In this chapter, we present synchronization mechanism appropriate for models of **shared memory systems**.

## 4.1 Synchronization by blocking

In an `if`-statement, an alternative is **executable** if its guard evaluates to `true`.
The choice of the alternative to execute is made nondeterministically among the executable alternatives.
If no guards evaluate to true, the `if`-statement itself is not executable.
Similarly, in a `do`-statement, if the guards of all alternatives evaluate to false, the statement is not executable and the process is blocked.

To say that **a process is blocked** means that in simulation mode SPIN will not choose the next statement to execute from that process.
In verification mode, it means that SPIN will not continue the search for a counterexample from this state by looking for states that can be reached by executing a statement from the process.
Hopefully, a subsequent execution of statements from other processes will **unblock** the blocked process, enabling it to continue executing in simulation mode, and in verificaiton mode, enabling the verifier to search for states reachable by executing a statement from the process.

> [!example] "Synchronization by busy-waiting"

```promela title="busy-waiting.pml" linenums="1" hl_lines="7 8 9 10 20 21 22 23"
bool wantP = false, wantQ = false;

active proctype P() {
  do
  :: printf("Noncritical section P\n");
    wantP = true;
    do
    :: !wantQ -> break
    :: else -> skip
    od;
    printf("Critical section P\n");
    wantP = false
  od
}

active proctype Q() {
  do
  :: printf("Noncritical section Q\n");
    wantQ = true;
    do
    :: !wantP -> break
    :: else -> skip
    od;
    printf("Critical section Q\n");
    wantQ = false
  od
}
```

- **busy waiting**: line 7-10, 20-23, perform no useful computation, just evaluate expressions repeatedly until they become true.

## 4.2 Executability of statements

An expression statement is **executable** if and only if it evaluates to true.

> [!example] "Synchronization with deadlock"

```promela title="deadlock.pml" linenums="1" hl_lines="7 17"
bool wantP = false, wantQ = false;

active proctype P() {
  do
  :: printf("Noncritical section P\n");
    wantP = true;
    !wantQ;
    printf("Critical section P\n");
    wantP = false
  od
}

active proctype Q() {
  do
  :: printf("Noncritical section Q\n");
    wantQ = true;
    !wantP;
    printf("Critical section Q\n");
    wantQ = false
  od
}
```

The concept of executability holds for every statement in PROMELA.
In the man page for each statement in PROMELA, there is a section that specifies the conditions for the statement to be executable.

## 4.3 State transition diagrams

Consider a program with two processes p and q that have $s_{p}$ and $s_{q}$ statements respectively, and two variables x and y that range over $v_{x}$ and $v_{y}$ values respectively.
The number of possible states that can appear in computations of the program is $s_{p} * s_{q} * v_{x} * v_{y}$.

The reachable states of a concurrent program can be visualized as a connected directed graph called a **state transition diagram**.
The nodes of the diagram are the reachable states and an edge exists from state s to state t if and only if there is a statement whose execution in s leads to t.

> [!example] "Abbreviated solution for the critical section problem"

Used in SPINSPIDER.

```promela linenums="1"
bool wantP = false, wantQ = false;

active proctype P() {
  do :: wantP = true;
    !wantQ;
    wantP = false
  od
}

active proctype Q() {
  do :: wantQ = true;
    !wantP;
    wantQ = false
  od
}
```

> TODO: add state transition diagram and anlysis it here.

## 4.4 Atomic sequences of statements

> [!example] "Atomic sequences of statements"

Easy solutions to the critical section problem using atomic statements:

```promela title="atomics.pml" linenums="1" hl_lines="6-9 18-21"
bool wantP = false, wantQ = false;

active proctype P() {
  do
  :: printf("Noncritical section P\n");
    atomic {
      !wantQ;
      wantP = true
    }
    printf("Critical section P\n");
    wantP = false
  od
}

active proctype Q() {
  do
  :: printf("Noncritical section Q\n");
    atomic {
      !wantP;
      wantQ = true
    }
    printf("Critical section Q\n");
    wantQ = false
  od
}
```

- Lines 6-9, 18-21 contain a potentially blocking expression and an assignment statement as one atomic sequence of statements.

### 4.4.1 `d_step` and `atomic`

The advantage of `d_step` is that it is extremely efficient because the statements of the sequence are executed or verified as a single step in a fully deterministic manner.
There are three limitations on `d_step`:

- except for the first statement in the sequence (the guard), statements cannot block.
- it's illegal to jump into the sequence or out of it using `goto` or `break`.
- nondeterminism is always resolved by choosing the first true alternative in a guarded command.

> [!example] "nondeterminism in `d_step`"

```promela
d_step {
    if
    :: a >= b -> max = a; branch = 1
    :: b >= a -> max = b; branch = 2
    fi
}
```

If `a` equals `b`, the value of `branch` will always equal 1.

`d_step` is usually reserved for fragments of sequential code, while `atomic` is preferred for implementing synchronization primitives.

> [!example] "Unreliable relay"

Process `Source` generates values for `input` and the process `Destination` prints the values of `output`.
Process `Relay` transfers data from the `Source` to the `Destination`.

The `atomic` sequence (lines 13-20) waits until the variable `input` has data and the waits until the variable `output` is empty; then is nondeterministically either transfer the value from `input` to `output` or it ignores the data.

```promela title="relay.pml" linenums="1" hl_lines="13-20"
#include "for.h"
byte input, output;

active proctype Source() {
  for (i, 1, 10)
    input == 0; /* Wait until empty */
    input = i
  rof (i)
}

active proctype Relay() {
  do
  :: atomic {
      input != 0;
      output == 0;
      if
      :: output = input
      :: skip /* Drop input data */
      fi
    }
    input = 0
  od
}

active proctype Destination() {
  do
  :: output != 0; /* Wait until full */
    printf("Output = %d\n", output);
    output = 0
  od
}
```

If `atomic` is replace by `d_step`, two problems occur:

- no data are ever dropped at line 18, since nondeterminism is resolved in favor of the first alternative.
- it's not legal to block at line 15.

## 4.5 Semaphores

??? note "Semaphore"

A definition of a semaphore using concepts of PROMELA:

A semaphore `sem` is a variable of type `byte` (nonnegative integers).
There are two atomic operations defined for a semaphore:

- `wait(sem)`: the operation is executable when the value of `sem` is positive, executing the operation decrements the value of `sem`.
- `signal(sem)`: the operation is always executable, executing the operation increments the value of `sem`.

> [!example] "The critical section problem with semaphores"

```promela title="cs-sem.pml" linenums="1"
byte sem = 1;

active proctype P() {
  do
  :: printf("Noncritical section P\n");
    atomic { /* wait(sem) */
      sem > 0;
      sem--
    }
    printf("Critical section P\n");
    sem++ /* signal(sem) */
  od
}

active proctype Q() {
  do
  :: printf("Noncritical section Q\n");
    atomic { /* wait(sem) */
      sem > 0;
      sem--
    }
    printf("Critical section Q\n");
    sem++ /* signal(sem) */
  od
}
```

## 4.6 Nondeterminism in models of concurrent systems

By design, SPIN does not contain constructs for modeling probability or for specifying that an event must occur with a certain probability.
The intended use of model checking is to detect errors that occur under complex scenarios that are unlikely to be discovered during system testing.

> In a well-designed system, erroneous behavior should be impossible, not just improbable. - SMC P.454

In SPIN, nondeterminism is used to model arbitrary values of data: whenever a value is needed, a nondeterministic choice is made among all values in the range.

### 4.6.1 Generating values nondeterministically

> [!example] "Generating values nondeterministically"

In a client-server system, the client nondeterministically chooses which request to make.

use an `if`-statement whose guard are always true:

```promela
active proctype Client() {
    if
    :: true -> request = 1
    :: true -> request = 2
    fi;
    /* Wait for service */
    if
    :: true -> request = 1
    :: true -> request = 2
    fi;
    /* Wait for service */
}
```

shorten: the assignment statements are always executable and can be used as guards

```promela
active proctype Client() {
    if
    :: request = 1
    :: request = 2
    fi;
    /* Wait for service */
    if
    :: request = 1
    :: request = 2
    fi;
    /* Wait for service */
}
```

- In a random simulation, SPIN randomly chooses which alternative of an `if`-statement to execute.
- In a verification, SPIN choose the first alternative and searches for a counterexcample; if one is not found, it **backtracks** and continues the search from the state that results from choosing the second alternative.

use `do`-statement to generate an unending stream of requests:

```promela
active proctype Client() {
    do
    :: request = 1;
        /* Wait for service */
    :: request = 2;
        /* Wait for service */
    od
}
```

### 4.6.2 Generating from an arbitrary range

> [!example] "Generating from an arbitrary range"

Choose nondeterministically values from an arbitrary range, from 0 to 9:

```promela
#define LOW 0
#define HIGH 9
byte number = LOW;
do
:: number < HIGH -> number++
:: break
od
```

Do not put any faith in the uniformity of the probability distribution of the 'random numbers' generated using this technique.
Nondeterminism is used to generate arbitrary computations for verification, not random numbers for a faithful simulation.

## 4.7 Termination of processes
### 4.7.1 Deadlock

If we run random simulations of the program in example 'Synchronization with deadlock', we will likely encounter a computation in which execution terminates with the output `timeout`.
This means that no statements are executable, a condition called **deadlock**.
An attempt at verification will discover an error called an **invalid end state**:

```shell
pan: invalid end state (at depth 8)
```

??? note "Invalid end state"

By default, a process that does terminate must do so after executing its last instruction, otherwise it is said to be in an invalid end state.

This error is check for regardless of any other correctness specifications, 
and this default behavior can be overridden.

### 4.7.2 End states

> [!example] "A client-server program with end states"

```promela title="client-server.pml" linenums="1"
byte request = 0;

active proctype Server1() {
  do
  :: request == 1 ->
    printf("Service 1\n");
    request = 0
  od
}

active proctype Server2() {
  do
  :: request == 2 ->
    printf("Service 2\n");
    request = 0
  od
}

active proctype Client() {
  request = 1;
  request == 0;
  request = 2;
  request == 0
}
```

If we simulate or verify this program in SPIN, we will receive an error message that there is an invalid end state: while the client executes a finite number of statements and then terminates, the servers are always blocked at the guard of the `do`-statement waiting for it to become executable.

We can indicate that a control point within a process is to be considered a valid end point even though it is not the last statement of the process by prefixing it with a label that begins with `end`:

```promela linenums="1" hl_lines="2"
active proctype Server1() {
endserver:
do
:: request == 1 -> . . .
od
}
```

An alternate way of ignoring end states is to ask SPIN to refrain from reporting invalid end states during a verification:

- jSpin: select `Options/Pan`, add argument `-E`.
- command line: `pan -E`.

### 4.7.3 The order of process termination

A process **terminates** when it has reached the end of its code, but it is considered to be an active process until it **dies**.

SPIN manages process allocation in the LIFO (last in first out) order of a stack,
so a process can **die** only if it is the most recent process that was created.

Processes created by `active proctype` are instantiated in the order written.

> [!example] "Client-server termination"

```promela title="client-server-termination.pml" linenums="1"
byte request = 0;
byte finished = 0;

active proctype Server1() {
  request == 1;
  request = 0;
  finished++
}

active proctype Server2() {
  request == 2;
  request = 0;
  finished++
}

active proctype Client() {
  request = 1;
  request == 0;
  request = 2;
  request == 0;
  finished == 2;
}
```

Output:

```shell
11: proc 2 (Client) terminates
11: proc 1 (Server2) terminates
11: proc 0 (Server1) terminates
```

Change line 21 to `finished == 3;`, output:

```shell
timeout
#processes: 3
2 Client 2 0
1 Server 2 0
0 Server 2 0
```

Move process `Client` to appear before the server processes in the source code, output:

```shell
timeout
#processes: 1
0 Client 2 0
```



# 5 Verification with Temporal Logic
Assertions are not sufficient to specify and verify most correctness properties of models.
This chapter presents **linear temporal logic (LTL)**, which is the formal logic used for verification in SPIN.

## 5.1 Beyond assertions

Assertions are limited in the properties that they can specify beacause they are attached to specific control points in the processes.

> [!example] "Properties not associated with specific control points"

- Mutual exclusion

In every state of every computation, `critical <= 1`.

**Absence of deadlock**: In every state of every computation, if some processes are trying to enter their critical sections, eventually some process does so.

**Absence of starvation**: In every state of every computation, if a process tries to enter its critical section, eventually that process does so.

- Absence of deadlock (invalid end states)

In every state of every computation, if no statements are executable, the location counter of each process must be at the end of the process or at a statement labeled `end`.

- Array index bounds

In every state of every computation, `0 <= i <= LEN - 1`.

- Quantity invariant

In **token-passing algorithms**, mutual exclusion is achieved by passing a **token** among the processes.

In every state of every computation, there is at most one token in existence.

## 5.2 Introduction to linear temporal logic
### 5.2.1 The syntax of LTL

| Operator   | Math              | SPIN  |
| :--------- | :---------------- | :---- |
| not        | $\neg$            | `!`   |
| and        | $\wedge$          | `&&`  |
| or         | $\vee$            | `     |  | ` |
| implies    | $\rightarrow$     | `->`  |
| equivalent | $\leftrightarrow$ | `<->` |
| always     | $\Box$            | `[]`  |
| eventually | $\Diamond$        | `<>`  |
| until      | $\mathcal{U}$     | `U`   |

### 5.2.2 The semantics of LTL

The semantics of a syntactically correct formula is defined by giving it an interpretation: an assignment of truthe values (true or false) to its atomic propositions and the extension of the assignment to an interpretation of the entire formula according to the rules for the operators.

For temporal lofic, the semantics of a formula is given in terms of computations and the states of a computation.

## 5.3 Safety properties

### 5.3.1 Expressing safety properties in LTL

??? note "Safety property"

Let $A$ be an LTL formula and let $\tau = (s_{0}, s_{1}, s_{2}, \cdots)$ be a computation.
Then $\Box A$, read always $A$, is true in state $s_{i}$ if and only if $A$ is true for all $s_{j}$ in $\tau$ such that $j \ge i$.

The formula $\Box A$ is called a **safety property** because it specifies that the computation is safe in that nothing bad ever happens.

### 5.3.2 Expressing safety properties in PROMELA

Atomic propositions in an LTL formula must be identifiers starting with a lower-case letter.
And they must be boolean variables or defined as symbols for boolean-valued expressions.

> [!example] "Expressing safety property in mutual exclusion"

- use a variable `critical`

```promela title="safety.pml" linenums="1" hl_lines="1 9-10"
#define mutex (critical <= 1)
bool wantP = false, wantQ = false;
byte critical = 0;

active proctype P() {
    do
    :: wantP = true;
        !wantQ;
        critical++;
        critical--;
        wantP = false;
    od
}

/* Similarly for process Q */
```

LTL formula: `[]mutex`.

- use two variables `csp` and `csq` of boolean type

```promela linenums="1" hl_lines="1"
bool wantP = false, wantQ = false;
bool csp = false, csq = false;

active proctype P() {
    do
    :: wantP = true;
        !wantQ;
        csp = true;
        csp = false;
        wantP = false;
    od
}

/* Similarly, for process Q */
```

LTL fomula: `[]!(csp && csq)`.

### 5.3.3 Verifying safety properties in SPIN

To verify safety properties in SPIN:

- jSpin: write the LTL formula in the text field and select `Translate`, the formula is saved in a file with the same name as the PROMELA source file and with extension `prp`, then SPIN is called to translate the formula into a never claim. select `Safety` for the verification mode and select `Verify`.
- command line: (1) add the **negation** of the LTL formula with the `-f` argument to the SPIN command that generates the verifier, (2) compile the verifier with `-DSAFETY` argument to optimize for checking safety properties, (3) run pan as usual.

> [!example] "Verify safety properties in command line"

```shell
spin -a -f "![]mutex" third-safety.pml
gcc -DSAFETY -o pan pan.c
pan
```

or

```promela title="safety.prp"
![]mutex
```

```shell
spin -a -F safety.prp third-safety.pml
```

or

```shell
## 5.save the never claim to file
spin -a -f "![]mutex" > safety.ltl
## 5.include the never claim file in the generation of the verifier
spin -a -N safety.ltl third-safety.pml
```

## 5.4 Liveness properties

??? note "Liveness property"

Let $A$ be an LTL formula and let $\tau = (s_{0}, s_{1}, s_{2}, \cdots)$ be a computation.
Then $\Diamond A$, read eventually $A$, is true in state $s_{i}$ if and only if $A$ is true for some $s_{j}$ in $\tau$ such that $j \ge i$.

The formula $\Box A$ is called a **liveness property** because it specifies that something good eventually happens in the computation.

### 5.4.1 Expressing liveness properties in SPIN

> [!example] "Critical section with starvation"

```promela linenums="1"
bool wantP = false, wantQ = false;

active proctype P() {
  do
  :: wantP = true;
    do
    :: wantQ ->
      wantP = false;
      wantP = true
    :: else -> break
    od;
    wantP = false
  od
}

active proctype Q() {
  do
  :: wantQ = true;
    do
    :: wantP ->
      wantQ = false;
      wantQ = true
    :: else -> break
    od;
    wantQ = false
  od
}
```

- Starvation may occur, there is a computation in which process `P` never enters its critical section.

### 5.4.2 Verifying liveness properties in SPIN

> [!example] "Verify liveness property in critical section with starvation"

```promela title="liveness.pml" linenums="1" hl_lines="13-14"
bool wantP = false, wantQ = false;
bool csp = false;    

active proctype P() {
  do
  :: wantP = true;
    do
    :: wantQ ->
      wantP = false;
      wantP = true
    :: else -> break
    od;
    csp = true;
    csp = false;
    wantP = false
  od
}

active proctype Q() {
  do
  :: wantQ = true;
    do
    :: wantP ->
      wantQ = false;
      wantQ = true
    :: else -> break
    od;
    wantQ = false
  od
}
```

LTL formula: `<>csp`.

To verify liveness properties in SPIN:

- jSpin: select `Acceptance` for the verification mode, check the box `Weak fairness`, select `Verify`.
- command line: `-a -f`, `-a` for acceptance, `-f` for weak fairness.

> [!example] "Verify liveness properties in command line"

```shell
spin -a -f "!<>csp" fourth-liveness.pml
gcc -o pan pan.c
pan -a -f
```

SPIN did not find the shortest counterexample.
The `-i` and `-I` arguments to `pan` can be used to perform an iterated search for shorter counterexamples.

## 5.5 Fairness

??? note "Weak fairness"

A computation is **weakly fair** if and only if the following condition holds: if a statement is always executable, then it is eventually executed as part of the computation.

To make computations weakly fair:

- jSpin: check the box `Weak fairness` before select `Verify`.
- command line: `pan -a -f`.

Restricting verification to computations that are weakly fair requires a lot of memory.
By default, SPIN limits the number of processes to two in a verification with fairness; we can use `-DNFAIR=n` to compile the verifier with more processes.

> [!example] "Termination under weak fairness"

```promela linenums="1"
int n = 0;
bool flag = false;

active proctype P() {
  do
  :: flag -> break
  :: else -> n = 1 - n
  od
}

active proctype Q() {
  flag = true
}
```

If weak fairness is not specified, there is a nonterminating computation in which the `do`-statement is executed indefinitely.

## 5.6 Duality

$$
\neg \Box p \equiv \Diamond \neg p \\
\neg \Diamond p \equiv \Box \neg p
$$

## 5.7 Verifying correctness without ghost variables

PROMELA supports **remote references** that can be used to refer to control points in correctness specifications, either directly within never claims or in LTL formulas.

It is also possible to refer to the value of a local variable of a process using the syntax `process:variable`.

A remote reference is not a symbol, so it cannot appear directly within an LTL formula.
It can appear in a boolean expression for which a symbol is defined.

> [!example] "Remote references"

```promela linenums="1" hl_lines="1 7"
#define mutex !(P@cs && Q@cs)

active proctype P() {
  do
  :: wantP = true;
      !wantQ;
cs:   wantP = false;
  od
}

/* Similarly for process Q */
```

- The expression `P@cs` returns a nonzero value if and only if the location counter of process `P` is at the control point labeled by `cs`.

## 5.8 Modeling a noncritical section

> [!example] "Modeling failure in the noncritical section"

```promela linenums="1" hl_lines="5-8"
byte turn = 1;

active proctype P() {
  do
  :: if
    :: true
    :: true -> false
    fi;
    turn == 1;
cs: turn = 2
  od
}

active proctype Q() {
  do
  :: turn == 2;
cs:  turn = 1
  od
}
```

- Lines 5-8 model the noncritical section: `P` can nondeterministically choose to do nothing (line 6) or to fail by blocking until `false` becomes true, which will never occur (line 7).

## 5.9 Advanced temporal specifications
### 5.9.1 Latching

$\Diamond \Box A$ expresses a **latching** property: $A$ may not be true initially in a computation, but eventually it becomes true and remain true.

### 5.9.2 Infinitely often

$\Box \Diamond A$ expresses the property that $A$ is true **infinitely often**: $A$ need not always be true, but at any state $s$ in the computation, $A$ will be true in $s$ or in some state that comes after $s$.

### 5.9.3 Precedence

$p \ \mathcal{U} \ q$ is true in state $s_{i}$ of a computation $\tau$ if and only if there is some state $s_{k}$ in $\tau$ with $k \ge i$, such that $q$ is true in $s_{k}$, and for all $s_{j}$ in $\tau$ such that $i \le j \lt k$, $p$ is true in $s_{j}$.

$\neg B \ \mathcal{U} \ A$: $B$ remains false until $A$ becomes true.

### 5.9.4 Overtaking

> [!example] "Peterson’s algorithm"

```promela title="peterson.pml" linenums="1"
#define ptry P@try
#define qcs Q@cs
#define pcs P@cs

bool wantP, wantQ;
byte last = 1;

active proctype P() {
  do
  :: wantP = true;
    last = 1;
try: (wantQ == false) || (last == 2);
cs: wantP = false
  od
}

active proctype Q() {
  do
  :: wantQ = true;
    last = 2;
try: (wantP == false) || (last == 1);
cs: wantQ = false
  od
}
```

one-bounded overtaking in Peterson's algorithm in LTL formula:

```promela
[](ptry -> (!qcs U (qcs U (!qcs U pcs))))
```

Note: the operator `U` defined in SPIN is left-associative.

### 5.9.5 Next

$\mathcal{X} A$ is true in a state $s_{i}$ of a computation if $A$ is true in the following state $s_{i+1}$.

The operator $\mathcal{X}$ called **next** and written `X` in SPIN.

*Without* this operator, temporal logic formulas are **stutter invariant**.
This means that any correctness specification that is true in a computation remains true if duplicate consecutive states are removed to form a more concise computation.
The algorithms in SPIN are more efficient if stutter-invariant specifications are used.


# 6 Data and Program Structures
PROMELA does have arrays and type definitions that are used for structuring data, and it has macros and inline declarations that can help make programs more readable.

## 6.1 Arrays

PROMELA includes the array, the syntax and semantics of arrays are similar to those of C-like languages.
Arrays in PROMELA are one-dimensional.

It is an error if the index is not within the bounds of an array: an error message will be printed during simulation (without terminating the computation) and the error will be reported when it is encountered during verification.

Arrays of type `bit` or `bool` are stored as arrays of type `byte`.

> [!example] "Computing the sum of the elements of an array of integer type"

```promela title="sum.pml" linenums="1"
#include "for.h"
active proctype P() {
  int a[5];
  a[0] = 0; a[1] = 10; a[2] = 20; a[3] = 30; a[4] = 40;
  int sum = 0;
  for (i, 0, 4)
    sum = sum + a[i]
  rof (i);
  printf("The sum of the numbers = %d\n", sum)
}
```

## 6.2 Type definitions

Compound types are defined with `typedef` and are primarily used for defining the structure of messages to be sent over channels.

> [!example] "Type definitions"

Message type over channels:

```promela
typedef MESSAGE {
  mtype message;
  byte source;
  byte destination;
  bool urgent
}
```

A two-dimensional array:

```promela
typedef VECTOR {
  int vector[10]
}

VECTOR matrix[5];
// ...
matrix[3].vector[6] = matrix[4].vector[7];
```

Data structure for a sparse array:

```promela title="sparse-array.pml" linenums="1" hl_lines="1"
#include "for.h"
#define N 4
typedef ENTRY {
  byte row;
  byte col;
  int value
}
ENTRY a[N];

active proctype P() {
  int i = 0;
  a[0].row = 0; a[0].col = 1; a[0].value = -5;
  a[1].row = 0; a[1].col = 3; a[1].value = 8;
  a[2].row = 2; a[2].col = 0; a[2].value = 20;
  a[3].row = 3; a[3].col = 3; a[3].value = -3;

  for (r, 0, N-1)
    for (c, 0, N-1)
      if
      :: i == N -> printf("0 ")
      :: i < N && r == a[i].row && c == a[i].col ->
        printf("%d ", a[i].value);
        i++
      :: else -> printf("0 ")
      fi
    rof (c);
    printf("\n")
  rof (r)
}
```

## 6.3 The preprocessor

Inclusion of source code is implemented by a compile-time software tool called the **preprocessor**, which is called before the compiler itself is executed.
The preprocessor is also used to conduct **text-based** macro processing on the source code.
Text-based means the preprocessor treats the source code as pure text.

When SPIN is run in any mode, it first calls a preprocessor.

> [!example] "Usage of preprocessor"

```promela
// include a file
#include "for.h"

// declare a symbol
#define N 4
// declare symbols for expressions used in correctness specifications
#define mutex (critical <= 1)
```

### 6.3.1 Condition compilation

The preprocessor can be used to implement **conditional compilation**, which enables the compile-time parameterization of a program.

> [!example] "Condition compilation"

```promela title="pri.pml"
#ifdef VerOne
  currentPriority = (p1 > p2 -> p1 : p2);
#endif
#ifdef VerTwo
  currentPriority = PMAX;
#endif
#ifdef VerThree
  currentPriority = PMIN;
#endif
```

run SPIN on this program with symbol `VerTwo` defined:

```shell
spin -DVerTwo pri.pml
```

Another technique that can be used instead of conditional compilation is to write a program (in any language) to generate PROMELA code for different versions of the model.

### 6.3.2 Macros

`#define` can be used to create macros that can improve the readability of PROMELA programs.

> [!example] "`for` macro"

```promela title="for.h"
#define for(I,low,high) \
  byte I; \
  I = low ; \
  do \
  :: ( I > high ) -> break \
  :: else ->

#define rof(I) \
  ; I++ \
  od
```

Run SPIN with `-I` to debug macros.
Use `-P` to support an alternate preprocessor to SPIN.

## 6.4 Inline

The `inline` construct gives a name to a sequence of statements.
Whenever the name of the inlined sequence is used within a `proctype`, the statements between the braces are copied to the corresponding position before compilation.
During the copy, the formal parameters appearing after the name of the inlined sequence are replaced by the actual parameters of the call.

The `inline` construct in SPIN is almost identical to the macro construct, but its syntax is more friendly, and errors will be reported with the line number within the `inline` construct, rather than with the line of the call.

> [!example] "Printing an array with `inline`"

```promela title="inlines.pml" linenums="1" hl_lines="4"
#include "for.h"
#define N 5

inline write(ar) {
  d_step {
    for (k, 0, N-1)
      printf("%d ", ar[k])
    rof (k);
    printf("\n")
  }
}

active proctype P() {
  int a[N];
  write(a);
  for (i, 0, N-1)
    a[i] = i
  rof (i);
  write(a)
}
```


# 7 Channels
Communicating Sequential Processes (CSP) was the inspiration for the channel construct in PROMELA.

## 7.1 Channels in PROMELA

A **channel** in PROMELA is a data type with two operations, **send** and **receive**.
Every channel has associated with it a **message type**, once a channel has been initialized, it can only send and receive messages of its message type.
At most 255 channels can be created.
The type of a message field cannot be an array; however, the type can be a `typedef`.

The channel is declared with an initializer specifying the **channel capacity** and the message type:

```promela
chan ch = [capacity] of { typename, ..., typename }
```

There are two types of channels with different semantics:

- rendezvous channels of capacity zero.
- buffered channels with capacity greater than zero.

The send statement consists of a channel variable followed by an exclamation point `!` and then a sequence of expressions whose number and types match the message type of the channel.
The receive statement consists of a channel variable followed by question mark `?` and a sequence of variables.

The expressions in the send statement are evaluated and their values are transferred through the channel;
the receive statement assigns these values to the variables listed in the statement.

A receive statement cannot be executable unless a message is available in the channel.

> [!example] "Client-server using channels"

```promela title="c-s.pml" linenums="1" hl_lines="1"
chan request = [0] of { byte };

active proctype Server() {
  byte client;
end:
  do
  :: request ? client ->
      printf("Client %d\n", client)
  od
}

active proctype Client0() {
  request ! 0
}

active proctype Client1() {
  request ! 1
}
```

The list of expressions `ch ! e1, e2, ...` can be written `ch ! e1(e2, ...)`.
This is primarily used when the first argument is an `mtype`, indicating the type of the message.

```promela
mtype { open, close, reset };
chan ch = [1] of { mtype, byte, byte };
byte id, n;

ch ! open, id, n;
ch ! open(id, n);
```

### 7.1.1 Channels and channel variables

The type of all channel variables is `chan` and a channel variable holds a reference or handle to the channel itself, which is created by an initializer.

A channel can be sent in a message and received by another process.

??? note "Local channels"

We can declare and initialize locally channels, and then pass to another process in a message.

If a channel is declared and initialized within a process and the process then dies, the channel is no longer accessible.

## 7.2 Rendezvous channels

A channel declared with a capacity of zero is a **rendezvous channel**.
This means that the transfer of the message from the sender to the receiver is **synchronous** and is executed as as single atomic operation.

A send statement that offers to engage in a rendezvous for which there is no matching receive statement is itself not executable, and similarly for an executable receive statement with no matching executable send statement.

> [!example] "Simple program with rendezvous"

```promela title="rendezvous.pml" linenums="1" hl_lines="2"
mtype { red, yellow, green };
chan ch = [0] of { mtype, byte, bool };

active proctype Sender() {
  ch ! red, 20, false;
  printf("Sent message\n")
}

active proctype Receiver() {
  mtype color;
  byte time;
  bool flash;
  ch ? color, time, flash;
  printf("Received message %e, %d, %d\n",
    color, time, flash)
}
```

### 7.2.1 Reply channels

> [!example] "Client-server with a reply channel"

```promela title="reply.pml" linenums="1" hl_lines="2"
chan request = [0] of { byte };
chan reply = [0] of { bool };

active proctype Server() {
  byte client;
end:
  do
  :: request ? client ->
    printf("Client %d\n", client);
    reply ! true
  od
}

active proctype Client0() {
  request ! 0;
  reply ? _
}

active proctype Client1() {
  request ! 1;
  reply ? _
}
```

> [!example] "Multiple clients and servers"

```promela linenums="1" hl_lines="4 15"
chan request = [0] of { byte };
chan reply = [0] of { byte };

active [2] proctype Server() {
  byte client;
end:
  do
  :: request ? client ->
    printf("Client %d processed by server %d\n",
      client, _pid);
    reply ! _pid
  od
}

active [2] proctype Client() {
  byte server;
  request ! _pid;
  reply ? server;
  printf("Reply received from server %d by client %d\n",
    server, _pid)
}
```

### 7.2.2 Arrays of channels

> [!example] "An array of channels"

```promela linenums="1" hl_lines="2"
chan request = [0] of { byte, chan };
chan reply [2] = [0] of { byte, byte };

active [2] proctype Server() {
  byte client;
  chan replyChannel;
end:
  do
  :: request ? client, replyChannel ->
    printf("Client %d processed by server %d\n",
      client, _pid);
    replyChannel ! _pid, client
  od
}

active [2] proctype Client() {
  byte server;
  byte whichClient;
  request ! _pid, reply[_pid2];
  reply[_pid2] ? server, whichClient;
  printf("Reply received from server %d by client %d\n",
    server, _pid);
  assert(whichClient == _pid)
}
```

### 7.2.3 Local channels

> [!example] "Local channels"

```promela title="local.pml" linenums="1" hl_lines="18"
chan request = [0] of { byte, chan };
    
active [2] proctype Server() {
  byte client;
  chan replyChannel;
end:
  do
  :: request ? client, replyChannel ->
    printf("Client %d processed by server %d\n",
      client, _pid);
    replyChannel ! _pid, client
  od
}

active [2] proctype Client() {
  byte server;
  byte whichClient;
  chan reply = [0] of { byte, byte };
  request ! _pid, reply;
  reply ? server, whichClient;
  printf("Reply received from server %d by client %d\n",
    server, _pid);
  assert(whichClient == _pid)
}
```

### 7.2.4 Limitations of rendezvous channels

Normally there are many more clients than servers.
If rendezvous channels were used, the number of clients actually being served can be no larger than the number of servers, the rest of the clients would be blocked.

> [!example] "Limitations of rendezvous channels"

```promela linenums="1" hl_lines="5 17"
chan request = [0] of { byte, chan };
chan reply [2] = [0] of { byte, byte };
int numClients = 0;

active [2] proctype Server() {
  byte client;
  chan replyChannel;
end:
  do
  :: request ? client, replyChannel ->
    printf("Client %d processed by server %d\n",
      client, _pid);
    replyChannel ! _pid, client
  od
}

active [4] proctype Client() {
  byte server;
  request ! _pid, reply[_pid2];
  numClients++;
  assert (numClients <= 2);
  numClients--;
  reply[_pid2] ? server
}
```

## 7.3 Buffered channels

A channel declared with a positive capacity is called a **buffered channel**:

```promela
chan ch = [3] of { mtype, byte, bool };
```

The capacity is the number of messages of the message type that can be stored in the channel.
The send and receive statements treat the channel as a FIFO (first in first out) queue.

When the channel is not full, the send statement is executable; 
and when the channel is not empty, the receive statement is executable.

When run SPIN with `-m`, instead of blocking when the channel is full, the send statement is executed but the content of the channel does not change so taht the message is lost.

## 7.4 Checking the content of a channel

Executing the normal send and receive statements commits a process to either performing the operation on the channel or blocking until the statement becomes executable.

### 7.4.1 Checking if a channel is full or empty

4 predefined boolean functions for checking a channel: `full`, `empty`, `nfull`, `nempty`.

> [!example] "Checking if the channel is full or empty"

```promela title="full-empty.pml" linenums="1" hl_lines="1"
chan request = [2] of { byte, chan};
chan reply[2] = [2] of { byte };

active [2] proctype Server() {
  byte client;
  chan replyChannel;
  do
  :: empty(request) ->
    printf("No requests for server %d\n", _pid)
  :: request ? client, replyChannel ->
    printf("Client %d processed by server %d\n", client, _pid);
    replyChannel ! _pid
  od
}

active [2] proctype Client() {
  byte server;
  do
  :: nfull(request) ->
    printf("Client %d waiting for nonfull channel\n", _pid);
  :: request ! _pid, reply[_pid-2] ->
    reply[_pid-2] ? server;
    printf("Reply received from server %d by client %d\n", server, _pid)
  od
}
```

### 7.4.2 Checking the number of messages in a channel

A predefined integer function `len(ch)` that returns the number of messages in channel `ch`.

!!! note ""

Use the functions `empty`, `nempty`, `full`, `nfull` instead of `len` whenever possible, because they can be used by the SPIN optimization called partial order reduction to improve the efficiency of verifications.

## 7.5 Random receive

The random receive statement receive messages from anywhere within the channel, not just at the head; it is denoted by the double question mark `??`.

The receive statment allows values to be used instead of variables.
A receive statement is executable if and only if tis variables and values match the values in the fields of a message:

- a variable matches any field whose value is of the correct type,
- a value matches a field if and only if it equals the value of the field.

Sometimes, the value is known only at runtime, for example, when it is the value of a parameter to the `proctype`, or it is the value of `_pid` that is different for each instantiation of the `proctype`.
`eval` is used to obtain **the current value of the variable** to use in the matching.

> [!example] "Random receive from a buffered channel"

```promela title="random-recv.pml" linenums="1" hl_lines="18"
chan request = [4] of { byte };
chan reply = [4] of { byte, byte };

active [2] proctype Server() {
  byte client;
end:
  do
  :: request ? client ->
    printf("Client %d processed by server %d\n",
      client, _pid);
    reply ! _pid, client
  od
}

active [4] proctype Client() {
  byte server;
  request ! _pid;
  reply ?? server, eval(_pid);
  printf("Reply received from server %d by client %d\n",
    server, _pid)
}
```

## 7.6 Sorted send

A send statement for a buffered channel inserts the message at the tail of the message queue in the channel.

With the sorted send statement, written `ch !! message`, the message is inserted ahead of the first message that is larger than it.
Fields of the message are interpreted as integer values, and if there are multiple fields, lexicographic ordering is used.

Sorted send can be used to model a data structure such as a priority queue.

> [!example] "Storing values in sorted order"

```promela title="sorted-send.pml" linenums="1" hl_lines="14 16 18"
chan ch = [3] of { byte };

inline getValue() {
  if
  :: n = 1
  :: n = 2
  :: n = 3
  fi
}

active proctype Sort() {
  byte n;
  getValue();
  ch !! n;
  getValue();
  ch !! n;
  getValue();
  ch !! n;
  ch ? n;
  printf("%d\n", n);
  ch ? n;
  printf("%d\n", n);
  ch ? n;
  printf("%d\n", n)
}
```

## 7.7 Copying the value of a message

The following statements copy the values of a message into three variables but does not remove it (use angle brackets `<>` to enclose a list of variables):

```promela
ch ? <color, time, flash>
ch ?? <color, time, flash>
```

## 7.8 Polling

A polling expression, written with square brackets `[]`, is side-effect free and can be used in a guard:

```promela
do
:: ch ?? [green, time, false] ->
  ch ?? green, time, false
:: else -> /* Do something else */
od
```

Polling receive statements are not the same as receive statements that do not receive message from a channel: `ch ?? <green, time, false>`.

Polling receive statements can also be used in a subexpression of a compound expression:

```promela
bool even = true;

do
:: even && ch ?? [green, time, false] ->
ch ?? green, time, false;
even = !even
:: else -> /* Do something else */
even = !even
od
```

## 7.9 Comparing rendezvous and buffered channels

Rendezvous channels are far more efficient.
Buffered channels, on the other hand, greatly increase the potential size of the state space.
Rendezvous channels are unique in that a single step of a computation causes changes in values of the location counters of more than one process.


# 8 Nondeterminism
## 8.1 Nondeterministic finite automata

> [!example] "NDFA (Nondeterministic Finite Automata)"

$a^{*}((bb)^{+} + bc^{*})$

### 8.1.1 `timeout`

In SPIN, occurrences of a timeout state can be detected.
The predefined boolean variable `timeout` is true if and only if there are no executable statements in any process.

> [!example] "`timeout`"

```promela
active proctype Watchdog() {
  timeout -> printf("Rejected ...\n")
}
```

- The guard `timeout` will not become executable until the main process is blocked.

### 8.1.2 Using verification to find accepting computations

> SKIP.

### 8.1.3 Finding all counterexamples

> SKIP.

### 8.1.4 $lambda$-transitions

> SKIP.

## 8.2 VN: Visualizing nondeterminism

VN is a software tool for visualizing the nondeterminism of an NDFA.

The program modes:

- `Random`: SPIN executes the program in random simulation mode. A single computation is created by randomly resolving the nondeterminacy.
- `Create`: SPIN executes the program in interactive simulation mode.
- `Find`: The assertion `assert(false)` is added to the end of the generated program and a verification is performed.
- `Next`: The verifier is run again to search for the nex counterexample, if any.

## 8.3 NP problems

> SKIP.


# 9 Advanced Topics in PROMELA
For more information see SMC and the man page.

## 9.1 Specifiers for variables

??? note "Specifier for variables"

- `hidden`: if a global variable is specified as `hidden`, its value will not be part of the states of the computation. We can alternatively use the anoymous variable `_`.
- `local`: if a global variable is specified as `local`, the variable can only accessed by one process. The only reason to declare a variable used by one process to be global is to enable it to be used in a never claim.
- `xr`, `xs`: these specifier can be applied to a channel variable and specify that a process has exclusive receive (`xr`) or exclusive send (`xs`) access to the channel.
- `show`: this specifier is used with the XSPIN environment.

## 9.2 Predefined variables
### 9.2.1 The anonymous variable

The predefined global anonymous variable `_` replaces dummy variable used in other languages, and has tha advantage that its value is not part of the states of a computation, so no memory is required to store it during a verification.

> [!example] "Solution of the dining philosophers problem"

```promela linenums="1" hl_lines="6-7 17"
chan forks[5] = [0] of { bool };

proctype Phil(byte n; chan left; chan right ) {
  do
  :: printf("Philosopher %d is thinking\n", n);
    left ? _;
    right ? _;
    printf("Philosopher %d is eating\n", n);
    right ! true;
    left ! true
  od
}

proctype Fork(chan ch) {
  do
  :: ch ! true;
    ch ? _
  od
}

init {
  atomic {
    run Fork(forks[0]);
    run Fork(forks[1]);
    run Fork(forks[2]);
    run Fork(forks[3]);
    run Fork(forks[4]);
    run Phil(0,forks[0],forks[1]);
    run Phil(1,forks[1],forks[2]);
    run Phil(2,forks[2],forks[3]);
    run Phil(3,forks[3],forks[4]);
    run Phil(4,forks[4],forks[0]);
  }
}
```

### 9.2.2 Process identifiers

The predefined variable `_pid` is read-only and local to each process;
it gives a unique number to each process as it is instantiated.
The variable is of type `pid` and takes value from 0 to 254.

The predefined variable `_nr_pr` is read-only and global;
its value is the number of active processes.

## 9.3 Priority
### 9.3.1 Simulation priority

A priority for a process can be specified either on an `active proctype` declaration or on a `run` statement that instantiates a process type declared by `proctype`:

```promela
active proctype Important( ... ) priority 10 {
...
}

proctype NotImportant( ... ) {
...
}

run NotImportant( ... ) priority 2;
```

In SPIN, priority is meaningful only in random simulation mode;
the specification `priority 10` for a process simply means that this process is ten times more likely than a process with default priority 1 to be chosen for execution.

### 9.3.2 Modeling priority with global constraints

```promela
bool ok;

proctype P( ... ) provided (ok) {
  ...
}
```

This specification is attached to a `proctype` declaration and includes the keyword `provided` followed by an expression; the expression becomes an additional guard on all the statements of the process. 

If another process sets the variable `ok` to false at any time, process `P` will no longer be selected for execution during a simulation, and states obtained by executing a statement from `P` will no longer be searched during a verification.
Only when a process resets `ok` to true, will statements from `P` become executable.

> [!example] "Modeling an interrupt handler with `provided`"

```promela linenums="1" hl_lines="4"
byte n = 0;
bool interrupt = false;

proctype Compute() provided (!interrupt) {
  n = n + 1
}

proctype Interrupt() {
  byte temp;
  interrupt = true;
  temp = n + 1;
  n = temp;
  interrupt = false
}

init {
  atomic {
    run Interrupt();
    run Compute()
  }
  (_nr_pr == 1);
  assert (n == 2)
}
```

- Process `Compute` models the ordinary computation, process `Interrupt` models the interrupt handler.
- The `provided` specification in line 4 ensures that the increment instruction in process `Compute` cannot be executed while the interrupt handler is executing.

The use of `provided` should be avoided if possible, because SPIN cannot perform the partial order reduction optimization when it is used.

## 9.4 Modeling exceptions

In PROMELA, an `unless`-block can be associated with a statement or sequence of statements and is executed only if its guard becomes executable.

> [!example] "Handling division by zero"

```promela linenums="1" hl_lines="8"
active proctype Divide() {
  int n = 1;
end:
  do
  :: {
      ch ? n;
      printf("%d\n", 100 / n)
    } unless {
      n == 0 ->
        printf("Attempt to divide by zero\n")
    }
  od
}
```

- The `unless`-block is used to avoid division by zero: before each statement in the block is executed, the guard of the unless is checked.

The `unless` construct should be reserved for situations where an event can occur at arbitrary points within the computation.

## 9.5 Reading from standard input

`STDIN` is a predefined read-only channel, which is connected to standard input.

> [!example] "`STDIN`"

```promela
byte version;
STDIN ? version;
currentPriority = (
  (version == 1) ? (p1 > p2 -> p1 : p2) :
  (version == 2) ? PMAX : PMIN );
```

## 9.6 Embedded C code

SPIN can simulate and verify PROMELA models with embedded C code.
The intention is taht algorithms written in C can form part of the model, even if SPIN cannot prove the algorithms themselves.


# 10 Advanced Topics in SPIN
## 10.1 How SPIN searches the state space

SPIN does not actually search the graph in the sense that the graph is constructed and then searched;
instead, for each transition that is considered, SPIN builds that target state on-the-fly.

## 10.2 Optimizing the performance of verifications
### 10.2.1 Writing efficient models

The data stored for each state, called the **state vector**, consist of the location counters of the processes and the values of the variables, for example `(4, 11, 0, 0)`.

Verification will be more efficient if the amount of memory needed to store a state vector is as small as possible, we can do these things to reduce memory usages:

- use as few processes as possible.
- do not declare unnecessary variables, and declare variables with as narrow a type as possible.
- avoid declaring channel capacities in excess of what is needed to verify the model.
- use `atomic` and `d_step` where possible.

### 10.2.2 Allocating memory for the hash table

SPIN uses a hash table to store the state vectors taht have been previously encountered.
The default for the number entries in the table is $2^{18}$, it can be increased using the `-w` argument when executing the verifier: `pan -w20`.

### 10.2.3 Compressing the state vector

SPIN implements a sophisticated method for encoding the state vector called **collapse compression**, which is invoked by compiling the verifier with an argument: `gcc -DCOLLAPSE (other arguments) -o pan pan.c`.

### 10.2.4 Minimal automaton

State vectors can be stored without a hash table using a representation called a **minimal automaton** that is similar to the binary decision diagrams used in other model checkers.
This is invoked with a compile-time argument that gives the size of the automaton: `gcc -DMA=10 (other arguments) -o pan pan.c`.

### 10.2.5 Partial-order reduction

Partial order reduction avoids creating states that cannot be affected by interleaving the execution for the processes.

A few constructs in PROMELA are not compatible with partial order reduction and should be avoided if possible: `_last`, `provided`, `enabled` and remote variable references.

## 10.3 Never claims

SPIN transforms a formula in temporal logic into a PROMELA construct called a **never claim**.
Just as a PROMELA program specifies an automaton whose state space is searched by the verifier, 
a never claim specifies an automaton whose state space is searched in parallel with the one that is defined by the PROMELA program.

### 10.3.1 A never claim for a safety property

With symbol `mutex` defined as `#define mutex (critical <= 1)`, the specification of safety: `[]mutex`.
The negation of the correctness specification `[]mutex` is translated into the never claim:

```promela
never { /* !([]mutex) */
T0_init:
  if
  :: (! ((mutex))) -> goto accept_all
  :: (1) -> goto T0_init
  fi;
accept_all:
  skip
}
```

### 10.3.2 A never claim for a liveness property

The never claim for `!<>csp` is:

```promela
never { /* !(<>csp) */
accept_init:
T0_init:
  if
  :: (! ((csp))) -> goto T0_init
  fi;
}
```

### 10.3.3 Never claims for other LTL formulas

The never claim for `![]<>csp` is:

```promela
never { /* !([]<>csp) */
T0_init:
  if
  :: (! ((csp))) -> goto accept_S4
  :: (1) -> goto T0_init
  fi;

accept_S4:
  if
  :: (! ((csp))) -> goto accept_S4
  fi;
}
```

### 10.3.4 Predefined constructs for use in never claims

These predefined variables and functions are used only in never claims:

- `_last` is a read-only and global variable, its values is the process ID of the last process from which a statement was executed.
- `pc_value` fuction returns an integer representing the current location counter of the process whose ID is given as a parameter to the function.
- `enabled` function returns true if and only if the process whose ID is given as a parameter to the function has an executable statement.
- `np_` is a read-only and global variable, its value is true in all states that are not progress states.

Remote references enable access from within a never claim to the current location counter of a process or the current value of a local variable.

## 10.4 Non-progress cycles

SPIN has the capability to verify some liveness properties without writing a correctness specification in temporal logic.

> [!example] "Non-progress cycles"

```promela linenums="1" hl_lines="6"
byte sem = 1;

active proctype P() {
  do
  :: atomic { sem > 0 ; sem = sem 1 }
progress:
    sem = sem + 1
  od
}
active proctype Q() {
  do
  :: atomic { sem > 0 ; sem = sem 1 }
    sem = sem + 1
  od
}
active proctype R() {
  do
  :: atomic { sem > 0 ; sem = sem 1 }
    sem = sem + 1
  od
}
```

What would it mean for process `P` to be starved?
The correctness specification can be falsified only if there is an infinite computation that does not include infinitely many occurrentces of the progress state.
In SPIN this is called a **non-progress cycle**.

To search for a non-progress cycle:

- jSpin: select `Non-progress`.
- command line: compile the generated verifier with `-DNP` and run the verifier with `-l`.

```shell
spin -a sem-prog.pml
gcc -DNP -o pan pan.c
pan -l
```

Non-progress cycle are implemented by generating a neve claim using `np_` that is true if no process is at a progress state.
There is a non-progress cycle if there is an acceptance cyle in whith `np_` is always true.


# 11 Case Studies
## 11.1 Channels as data structures

## 11.2 Nondeterministic algorithms
### 11.2.1 The eight-queens problem
### 11.2.2 Cycles in a directed graph

## 11.3 Modeling a real-time scheduling algorithm
### 11.3.1 Real-time systems
### 11.3.2 Modeling a scheduler in PROMELA
### 11.3.3 Simplifying the model
### 11.3.4 Modeling a scheduler with priorities
### 11.3.5 Rate monotonic scheduling

## 11.4 Fischer’s algorithm

## 11.5 Modeling distributed systems

## 11.6 The Chandy–Lamport algorithm for global snapshots

## 11.7 The Chandy–Lamport snapshot algorithm in PROMELA
### 11.7.1 Structure of the program
### 11.7.2 Encoding lists of channels
### 11.7.3 The environment node
### 11.7.4 Local data for each node
### 11.7.5 Nodes of the distributed system
### 11.7.6 Nondeterministic choice of a channel

## 11.8 Verification of the snapshot algorithm


# A Software Tools
## A.1 SPIN
## A.2 JSPIN
## A.3 SPINSPIDER
## A.4 VN: Visualizing nondeterminism

# Links

# References

