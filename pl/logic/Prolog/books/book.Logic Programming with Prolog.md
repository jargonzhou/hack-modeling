# Logic Programming with Prolog

- Prolog stands for **Pro** gramming in **Log** ic.
- Version: SWI-Prolog 6.2.6 in book.

# Introduction
> [!example] "facts, rules, queries"

```Prolog

dog(fido).

dog(rover).

dog(henry).

cat(felix).

cat(michael).

cat(jane).

animal(X):-dog(X).

```

```Prolog

?- dog(fido).

true.

?- dog(jane).       /* Is jane a dog? No - a cat */

false.

?- animal(fido).   /* Is fido an animal? */

true.              /* yes - because it is a dog and any dog is an animal */

?- dog(X).         /* Is it possible to find anything, let us call it X, that is a dog? */

X = fido;          /* All 3 possible answers are provided */

X = rover;

X = henry

?-animal(felix).   /* felix is a cat and so does not qualify as an animal, as far as the program is concerned */

false.

```

Prolog implementations:

- [Amzi! Prolog](http://www.amzi.com/products/prolog_products.htm)

- [B-Prolog](http://www.probp.com/)

- [Ciao Prolog](http://clip.dia.fi.upm.es/Software/Ciao/)

- [GNU Prolog](http://gnu-prolog.inria.fr/)

- [Logic Programming Associates Prolog](http://www.lpa.co.uk): versions for Windows, DOS and Macintosh

- [PD Prolog](http://www-2.cs.cmu.edu/afs/cs/project/ai-repository/ai/lang/prolog/impl/prolog/pdprolog/0.html): a public domain version for MS-DOS only

- [SICStus Prolog](http://www.sics.se/isl/sicstuswww/site/index.html)

- [SWI Prolog](http://www.swi-prolog.org/): public domain versions for Windows, Linux and Macintosh

- [Turbo Prolog](http://www.fraber.de/university/prolog/tprolog.html): an old version that only runs in MS-DOS

- [Visual Prolog](http://www.visual-prolog.com/)

- [W-Prolog](http://waitaki.otago.ac.nz/~michael/wp/): a Prolog-like language that runs in a web browser

- [YAP Prolog](http://www.ncc.up.pt/~vsc/Yap/)
  

The programs in this book are all written using the standard **Edinburgh syntax** and should run unchanged in virtually any version of Prolog you encounter.

All the examples given have been tested using version 6.2.6 of SWI-Prolog.

# 1 Getting Started

## 1.1 Starting Prolog

The prompt `?-` indicates that the Prolog system is ready for the user to enter a sequence of one or more **goals**, which must be terminated by a full stop.

> [!example] "Starting Prolog"

```Prolog

?- write('Hello World'),nl,write('Welcome to Prolog'),nl.

Hello World

Welcome to Prolog

true.

?- halt.

?- statistics.

0.250 seconds cpu time for 61,957 inferences

4,179 atoms, 2,858 functors, 1,936 predicates, 36 modules, 62,926 VM-codes

1 garbage collections gained 14,448 bytes in 0.000 seconds.

Stack shifts: 2 local, 1 global, 1 trail in -0.000 seconds.

true.

```

- The meaning of `write` and `nl` are pre-defined by the Prolog system. They are known as **built-in predicates (BIPs)**.

- `halt` causes the Prolog system to terminate.

A sequence of one or more goals entered by the user at the prompt is often called a **query**.

We will generally use the term **sequence of goals** in this book.

## 1.2 Prolog Programs

> [!example] "Prolog Programs"

```Prolog title="prog1.pl"

dog(fido).

cat(felix).

animal(X) :- dog(X).

```

- `dog` is called a **predicate**, it has one argument, the word `fido` enclosed in `()`. `fido` is called an **atom** (meaning a constant which is not a number).

- `animal(X) :- dog(X).`: The `:-` character can be read as 'if'. `X` is called a **variable**. The rule can be read in a natural way as X is an animal if X is a dog (for any X).

```Prolog

?-consult('prog1.pl').         /* load program for use by the Prolog system */

% prog1.pl compiled 0.02 sec.

true.

?- animal(fido).

true.

?- animal(felix).

false.

```

> [!example] "Animals Program 1"

```Prolog title="animals1.pl"

/* Animals Program 1 */

dog(fido).

cat(mary). dog(rover).

dog(tom). cat(harry).

dog(henry).

cat(bill). cat(steve).

/* Apart from comments and blank lines, which are

ignored, Prolog programs consist of a number of

clauses. A clause is always terminated by a full

stop. It may run over more than one line, or there

may be several on the same line, separated by at

least one space. There are two types of clause:

facts and rules. dog(tom) is an example of a fact */

```

```Prolog

?-consult('animals1.pl').

% animals1.pl compiled 0.00 sec.

true.

/* queries */

?-dog(fido).

true.

?-dog(daisy).

false.

?- dog(X).

X = fido         /* pauses – user presses return key */

?- dog(Y).

Y = fido ;       /* pauses – user presses ; */

Y = rover ;      /* pauses – user presses ; */

Y = tom ;        /* pauses – user presses ; */

Y = henry        /* No pause – goes on to next line */

?- cat(X).

X = mary ;       /* pauses – user presses ; */

X = harry        /* pauses – user presses return */

?- listing(dog). /* List all the clauses defining predicate dog */

dog( fido ).

dog( rover ).

dog( tom ).

dog( henry ).

true.

?-cat(X),dog(Y). /* all possible combinations of a dog and a cat */

X = mary ,

Y = fido ;

X = mary ,

Y = rover ;

X = mary ,

Y = tom ;

X = mary ,

Y = henry ;

...

?-cat(X),dog(X). /* all animals which are both a cat and a dog */

false.

```

## 1.3 Data Objects in Prolog: Prolog Terms

The data objects in Prolog are called **terms**. Examples: `fido`, `dog(henry)`, `X`, `Y`.

types of terms:

- Numbers

All versions of Prolog allow the use of integers.

Most versions of Prolog also allow the use of numbers with decimal points.

> [!example] "Numbers"

```Prolog

623

-47

+5

025

6.43

-.245

+256

```

- Atoms

Atoms are constants that do not have numerical values: (a) any sequence of one or more letters (upper or lower case), numerals and underscores, beginning with a lower case letter; (b) any sequence of characters enclosed in single quotes, including spaces and upper case letters; (c ) any sequence of one or more special characters from a list that includes `+-*/><=&#@`.

> [!example] "Atoms"

```Prolog

john

today_is_Tuesday

fred_jones

a32_BCD

'Today is Tuesday'

'today-is-Tuesday'

'32abc'

+++

>=

>

+-

```

- Variables

In a query, a variable is a name used to stand for a term that is to be determined.

The name of a variable is denoted by any sequence of one or more letter (upper or lower case), numerals and underscores, beginning with an upper case letter or underscore.

> [!example] "Variables"

```Prolog

X

Author

Person_A

_123A

_        /* anonymous variable */

```

- Compound Terms

A compound term is a structured data type taht begins with an atom, known here as a **functor**.

The functor is followed by a sequence of one or more **arguments**, which are enclosed in brackets and separated by commas.

The general form is `functor(t1, t2, ..., tn), n >= 1`.

The number of arguments a compound term has is called its **arity**.

Each argument of a compound term must be a term, which can be of any kond including a compound term.

> [!example] "Compound Terms"

```Prolog

likes(paul,prolog)

read(X)

dog(henry)

cat(X)

>(3,2)

person('john smith',32,doctor,london)

likes(dog(henry),Y)

pred3(alpha,beta,gamma,Q)

pred(A,B,likes(X,Y),-4,pred2(3,pred3(alpha,beta,gamma,Q)))

```

- Lists

Lists are written as an unlimited number of arguments (known as **list elements**) enclosed in square brackets and separated by commas.

An element of a list may be a term of any kind, including a compound term or another list.

> [!example] "Lists"

```Prolog

[dog,cat,y,mypred(A,b,c),[p,q,R],z]

[[john,28],[mary,56,teacher],robert,parent(victoria,albert),[a,b,[c,d,e],f],29]

[[portsmouth,edinburgh,london,dover],[portsmouth,london,edinburgh],[glasgow]]

[]     /* empty list */

```

- Others

Some dialets of Prolog allow other types of term, e.g. **character strings**.
  

Atoms and compound terms have a special importance in Prolog clauses and are known collectively as **call terms**.

# 2 Clauses and Predicates

## 2.1 Clauses

Apart from commments and blank lines, which are ignored, a Prolog program consists of a succession of clauses.

There are 2 types of clauses: **facts** and **rules**.

```Prolog
/* facts */
head.

/* rules */
head :- t1, t2, ..., tk. /* k >= 1*/
```

- `head`: the **head** of the clause, it must be an atom or a compound term.
- `:-`: the **neck** of the clause (the neck operator), it is read as 'if'.
- `t1, t2, ..., tk`: the **body** of the clause, it specifies the conditions that must be met in order for the conclusion, represented by the head, to be satisfied. The body consists of one or more components, separated by commas, the components are **goals** and the commas are read as 'and'.
- Each goal must be a call term.
- A rule can be read as 'head is true if t1, t2, ..., tk are all true'.
- The head of a rule can also be viewed as a goal with the components of its body viewed as subgoals.

> [!example] "facts, rules"

```Prolog
christmas.
likes(john,mary).
likes(X,prolog).
dog(fido).

large_animal(X) :- animal(X),large(X).
grandparent(X,Y) :- father(X,Z),parent(Z,Y).
go :- write('hello world'),nl.
```

> [!example] "Animals Program 2"

```Prolog
/* Animals Program 2*/
dog(fido). large(fido).
cat(mary). large(mary).
dog(rover). dog(jane).
dog(tom). large(tom). cat(harry).
dog(fred). dog(henry).
cat(bill). cat(steve).
small(henry). large(fred).
large(steve). large(jim).
large(mike).

large_animal(X) :- dog(X),large(X).
large_animal(Z) :- cat(Z),large(Z).
```

## 2.2 Predicates

All the clauses (facts and rules) for which the head has a given combination of functor and arity comprise a definition of a **predicate**.

`listing(mypred)` gives a listing of all the clauses for predicate `mypred` whatever the arity.

> [!example] "Predicates"

```Prolog
/* parent/2 */
parent(victoria,albert).
parent(X,Y) :- father(X,Y).
parent(X,Y) :- mother(X,Y).
father(john,henry).
mother(jane,henry).

/* parent/1 */
parent(john).
parent(X) :- son(X,Y). /* X is a parent if X has a son Y */

animal(parent).

christmas.
/* go/0 */
go :- parent(john,B),
    write('john has a child named '),
    write(B),nl.
```

> [!note] "Declarative and Procedural Interpretations of Rules"

Rules have both a **declarative** and a **procedural** interpretation.

```Prolog
chases(X,Y) :- dog(X),cat(Y),write(X),
    write(' chases '),write(Y),nl.
```

- The declarative interpretation: `chases(X,Y)` is true if `dog(X)` is ture and `cat(Y)` is true and `write(X)` is true, etc.
- The procedural interpretation: to satisfy `chases(X,Y)`, first satisfy `dog(X)`, then satisfy `cat(Y)`, then satisfy `write(X)`, etc.

Facts are generally interpreted declaratively, e.g. `dog(fido)` is read as 'fido is a dog'.

The **order** of the clauses defining a predicate and the **order** of the goals in the body of each rule are irrelevant to the declarative interpretation but of vital importance to the procedural interpretation and thus to determing whether or not the sequence of goals entered by the user at the system prompt is satisfied.

A user's program comprises facts and rules that define new predicates.
These are called **user-defined predicates**.
In addition, there are standard predicates predefined by the Prolog system.
There are known as **built-in predicates (BIPs)**, and may not be redefined by a user program, e.g. `write/1`, `nl/0`.

> [!note] "Simplifying Entry of Goals"

```Prolog
?-dog(X),large(X),write(X),write(' is a large dog'),nl.
```

```Prolog
go :- dog(X),large(X),write(X),
    write(' is a large dog'),nl.
?-go.
```

> [!note] "Recursion"

An importance technique for defined predicates, is to define them in terms of themselves.
This is known as a **recursive definition**.

There are two forms of recursion:

- **direct recursion**: predicate `pred1` is defined in terms of itself.
- **indirect recursion**: predicate `pred1` is defined using `pred2`, which is defined using `pred3`, ..., which is defined using `pred1`.

```Prolog
likes(john,X) :- likes(X,Y),dog(Y).
```

> [!note] "Predicates and Functions"

The use of term **predicate** in Prolog is closely related to its use in mathematics.
Prolog does not make use of functions except in arithmetic expression.

## 2.3 Loading Clauses

Using the BIP `consult/1` causes the clauses contained in a text file to be loaded into the database as a side effect.
A Prolog program is just a collection of clauses (rules and facts) so we will refer to a file used this way as a **program file**.

> [!example] consult/1

```Prolog title="testfile.pl"
alpha.
beta.

dog(fido).
dog(misty).
dog(harry).

cat(jane).
cat(mary).
```

put all 7 of the above clauses into the database:

```Prolog
?-consult('testfile.pl').
```

change the file `testfile.pl`:

```Prolog title="testfile.pl"
gamma.

dog(patch).

elephant(dumbo).
elephant(fred).
```

remove all the clauses placed in the database by the first `consult/1`, and replace by the contents of the second version of `testfile.pl`:

```Prolog
?-consult('testfile.pl').
```

```Prolog
?-['testfile.pl'].                /* simplified notation of consult/1 */
?-consult('testfile.pl').

/* filenames are relative to the directory from which Prolog started up. */
?-consult('/mydir/testfile.pl').
?-['../../mydir/testfile.pl'].
```

break a program into several files and load them separately:

```Prolog title="testfile1.pl"
alpha.
beta.

dog(fido).
dog(misty).
dog(harry).

cat(jane).
cat(mary).
```

```Prolog title="testfile2.pl"
gamma.

dog(patch).

elephant(dumbo).
elephant(fred).
```

```Prolog
?-consult('testfile1.pl'), consult('testfile2.pl').
```

places these clauses in the database:

```Prolog
gamma.            /* loaded testfile2.pl */
alpha.
beta.

dog(patch).       /* delete dog/1 in testfile1.pl, replaced by dog/1 in testfile2 */

cat(jane).        /* loaded from testfile1.pl */
cat(mary).

elephant(dumbo).  /* loaded testfile2.pl */
elephant(fred).
```

`?-consult('testfile1.pl'), consult('testfile2.pl').` and `?-consult('testfile2.pl'), consult('testfile1.pl').` would give different results as far as the `dog/1` predicate is concerned.


## 2.4 Variables

Variables can be used in the head or body of a clause and in goals entered at the system prompt.

> [!example] "Animals Program 3"

```Prolog title="animals3.pl"
/* Animals Program 3 */
/* As Animals Program 2 but with the additional rules given below */
chases(X,Y) :- /* chases is a predicate with two arguments*/
    dog(X),cat(Y),
    write(X),write(' chases '),write(Y),nl.
    
go :- chases(A,B). /* go is a predicate with no arguments */
```

> [!note] "Variables in Goals"

Variables in goals can be interpreted as meaning 'find values of the variables that make the goal satisfied'. e.g. the goal `?-large_animal(A).` can be read as 'find a value of A such that large_animal(A) is satisfied'.

```Prolog
?-consult('animals3.pl').
%animals3.pl compiled 0.02 sec.

?- chases(X,Y).
fido chases mary
X = fido ,
Y = mary ;
fido chases harry
X = fido ,
Y = harry

?-chases(D,henry).
false.

?-go.
fido chases mary
true;
fido chases harry
true;
fido chases bill
true
```

- `?- chases(X,Y).` means find values of variables X and Y to satisfy `chases(X,Y)`.

```Prolog
chases(fido,mary) :- fchasesm.
chases(fido,john).
chases(fido,mary) :- freallychasesm.
fchasesm.
freallychasesm.

?- chases(fido,X).
X = mary ;
X = john ;
X = mary
```

> [!note] "Binding Variables"

Initially all variables used in a clause are said to be **unbound**, meaning that they do not have values.
Where the Prolog system evaluates a goal some variables may be given values such as `dog`, `-6.4` etc. This is known as **binding** the variables.

A variable that has been bound may become unbound again and possibly then bound to a different value by the process of **backtracking**.

> [!note] "Lexical Scope of Variables"

```Prolog
parent(X,Y) :- father(X,Y).

parent(First_person,Second_person) :-
    father(First_person,Second_person).
```

The variables X and Y are entirely unrelated to any other variables with the same name used elsewhere.
All occurrences of variables X and Y in the clause can be replaced consitently by any other variables, e.g. `First_person` and `Second_person`.

The **lexical scope** of a variable is the clause in which it appears.

> [!note] "Universally Quantified Variables"

If a variable appears in the head of a rule or fact it is taken to indicate that the rule or fact *applies for all possible values of the variable*

```Prolog
large_animal(X) :- dog(X),large(X).
```

can be read as 'for all values of X, X is a large animal if X is a dog and X is large'.

Variable X is said to be **universally quantified**.

> [!example] person`, `man

```Prolog
/* person/5 */
person(frances,wilson,female,28,architect).
person(fred,jones,male,62,doctor).
person(paul,smith,male,45,plumber).
person(martin,williams,male,23,chemist).
person(mary,jones,female,24,programmer).
person(martin,johnson,male,47,solicitor).

/* for all A, A is a man if A is a person whose sex is male */
man(A) :- person(A,B,male,C,D).
```

> [!note] "Existentially Quantified Variables"

- `B`, `C`, `D` in `man(A) :- person(A,B,male,C,D).`: for at least one value of `B`, etc.

The convention used by Prolog is that if a variable, say Y, appears in the body of a clause but not in its head it is taken to mean 'there is (or there exists) at least one value of Y'.
Such variables are said to be **existentially quantified**.

```Prolog
dogowner(X) :- dog(Y),owns(X,Y).
```

can be interpreted as meaning 'for all values of X, X is a dog owner if there is some Y such that Y is a dog and X owns Y'.

> [!note] "The Anonymous Variable"

The underscore character `_` denotes a special variable, called the **anonymous variable**.
This is used when the user does not care about the value of the variable.

```Prolog
?- person(paul,Surname,Sex,Age,Occupation).
Surname = smith ,
Sex = male ,
Age = 45 ,
Occupation = plumber

?- person(paul,_,_,_,_).
true.

?- person(paul,Surname,_,_,_).
Surname = smith

?- person(martin,_,_,Age,_).
Age = 23;
Age = 47

?- person(martin,X,X,Age,X).
false.
```

# 3 Satisfying Goals

## 3.1 Introduction

> [!example] "How Prolog satisfies goals"

The process begins when the user enters a sequence of goals at the system prompt:

```Prolog
?- owns(X,Y),dog(Y),write(X),nl.
```

The Prolog system attempst to satisfy each goal in turn, working **from left to right**.
When the goal involves variables, e.g. `owns(X,Y)`, this generally involves binding them to values, e.g. `X` to `john` and `Y` to `fido`.

If all the goals succeed in turn, the whole sequence of goals succeeds.
The system will output the values of all the variables that are used in the sequence of goals and any other text ouput as a side effect by goals such as `write(X)` and `nl`.

```Prolog
?- owns(X,Y),dog(Y),write(X),nl.
john
X = john,
Y = fido
```

If it is not possible to satisfy all the goals (simultaneously), the sequence of goals will fail.

```Prolog
?- owns(X,Y),dog(Y),write(X),nl.
false.
```

> [!note] "Call Terms"

Every goal must be a Prolog term, it may only be an **atom** or a **compound term**, not a number, variable, list or any other type of term provided by some particular implementation of Prolog.
This restrict type of term is called a **call term**.
Heads of clauses and goals in the bodies of rules must also be call terms.

Every goal such as `write('Hello World')`, `nl`, `dog(X)` and `go` has a corresponding **predicate**, in this case `write/1`, `nl/0`, `dog/1` and `go/0` respectively.
The name of the predicate is called the **functor**.
The number of arguments it has is called the **arity**.

Goals relating to built-on predicates are evaluated in a way pre-defined by the Prolog system, as was discussed for `write/1` and `nl/0`.
Goals relating to user-defined predicates are evaluated by examing the database of rules and facts loaded by the user.

Prolog attempts to satisfy a goal by matching it with the heads of clauses in the database, working **from top to bottom**.

A fundamental principle of evaluating user-defined goals in Prolog is that any goal that cannot be satisfied using the facts and rules in the database **fails**.
There is no intermediate position, such as 'unknown' or 'not proven'.
This is equivalent to making a very strong assumption abount the database called the **closed world assumption**: any conclusion that cannot be proved to follow from the facts and rules in the data base is false.

## 3.2 Unification

Given a goal to evaluate, Prolog works through the clauses in the database trying to match the goal with each clause in turn, working from top to bottom until a match is found.
If no match is found the goal fails.

Prolog uses a very general form of matching known as **unification**, which generally involves one or more variables being given values in order to make two call terms identical.
This is known as **binding** the variable to values.

> [!example] "Term Unification"

```Prolog
dog(X)
dog(fido)

owns(john,fido)
owns(P,   Q)
```

Initially all variables are **unbound**, i.e. do not have any value.
Unlike for most other programming languages, once a variable has been bound it can be make unbound again and then perhaps be bound to a new value by **backtracking**.

### 3.2.1 Unifying Call Terms

The process of unify call terms:

```
Are call terms both constants?
[Y] Succeeds if they are the same constant, otherwise fails.
[N] Are call terms both compound terms?
[Y] Same functor and arity?
    [Y] Do arguments unify pairwise?
        [Y] Succeeds
        [N] Fails
    [N] Fails
[N] Fails
```

The process of unifying two terms:

```
1. Two atoms unify if and only if they are the same.

2. Two compound terms unify if and only if they have the same functor and the same arity 
   and their arguments can be unified pairwise, working from left to right.

3. Two numbers unify if and only if they are the same, so 7 unifies with 7, but not with 6.9.

4. Two unbound variables, say X and Y always unify, with the two variables bound to each other.

5. An unbound variable and a term that is not a variable alwyas unify, with the variable bound to the term.

- X and fido unify, with variable X bound to the atom fido
- X and [a,b,c] unify, with X bound to list [a,b,c]
- X and mypred(a,b,P,Q,R) unify, with X bound to mypred(a,b,P,Q,R)

6. A bound variable is treated as the value to which it is bound.

7. Two lists unify if and only if they have the same number of elements 
   and their elements can be unified pairwise, working from left to right.

- [a,b,c] can be unified with [X,Y,c], with X bound to a and Y bound to b
- [a,b,c] cannot be unified with [a,b,d]
- [a,mypred(X,Y),K] can be unified with [P,Z,third], 
  with variables P, Z and K bound to a atom a, compound term mypred(X,Y) and atom third, respectively 

8. All other combination of terms fail to unify.
```

> [!example] "Unification visually"

```Prolog
person(X,   Y,    Z)
person(john,smith,27)
/* Succeeds with variables X, Y and Z bound to john, smith and 27, respectively */

person(john,Y,    23)
person(X,   smith,27)
/* Fails because 23 cannot be unified with 27 */

pred1(X,Y,     [a,b,c])
pred1(A,prolog,B)
/* Succeeds with variables X and A bound to each other, Y bound to atom prolog and B bound to list [a,b,c] */
```

Repeated Variables:

```Prolog
pred2(X,     X,  man)
pred2(london,dog,A)
/* Fails because X cannot unify with both the atoms london and dog */

pred3(X,     X,     man)
pred3(london,london,A)
/* Succeeds with variables X and A bound to atoms london and man, respectively */

pred(alpha,beta,mypred(X, X,  Y))
pred(P,    Q,   mypred(no,yes,maybe))
/* Fails */

pred(alpha,beta,mypred(X, X, Y))
pred(P,    Q,   mypred(no,no,maybe))
/* Succeeds with variables P, Q, X andY bound to atoms alpha, beta, no and maybe, respectively */
```

## 3.3 Evaluating Goals

Given a goal such as `go` or `dog(X)`, Prolog searches through the database from top to bottom examining those clauses that have heads with the same functor and arity until it finds the first one for which the head unifies with the goal.

- (1) If there are none, the goal *fails*.
- (2) If it does make a successful unification, the outcome depdends on whether the clause is a *rule* or a *fact*.
- (2.1) If the clause is a *fact*, the goal *succeeds* immediately.
- (2.2) If it is a *rule*, Prolog evaluates the goals in the body of the rule one by one, from left to right. If they all succeed, the original goal *succeeds*.

We will use the phrase **'a goal matches a clause'** to mean that it unifies with the head of the clause.

> [!example] "Evaluating Goals"

```Prolog
capital(london,england).

/* Rule 1*/
pred(X,'european capital') :-
    capital(X,Y),european(Y),write(X),nl.
/* Rule 2 */
european(england) :- write('God Save the Queen!'),nl.

/* query */
?-pred(london,A).
```

```Prolog
?-pred(london,A).

  pred(X,     'european capital') :-
    capital(X,     Y), european(Y),write(X),nl.
    capital(london,england).
                       european(england) :- write('God Save the Queen!'),nl.

God Save the Queen!
london
A = 'european capital'
```

The process of evaluating a sequence of goals:

```
(1) Are there more goals?
[Y] (2) Evaluate next goal
[Succeeds] goto (1)
[Fails] See Section 3.4 Backtracking
[N] Sequence of goals succeeds
```

The process of evaluating a goal:

```
(1) Is predicate a BIP?
[Y] Goal is evaluated as predefined by system (may succeed or fail)
[N] (2) Are there more clauses in the database?
[Y] (3) Can the goal be unified with head of next clause?
    [Y] Evaluate body of clause (a sequence of goals)
        [Succeeds] Goal succeeds
        [Fails] goto (2)
    [N] goto (2)
[N] Goal fails
```

## 3.4 Backtracking

**Backtracking** is the process of going back to a previous goal and trying to *resatify* it, i.e. to find another way of satifying it.

- backtracks: it goes back to the most recently satisfied goal in the body of rule, moving **from right to left**, and tries to resatify it, i.e. to find another way of satisfying it.
- `write/1` and `nl/0` are **unresatisfiable**, meaning that always fails when evaluated during backtracking.
- The user can force the system to backtrack to find a further solution or solutions by entering a semicolon character `;`. This works by forcing the most recently satisfied goal to fail.

> [!example] "The Family Relationships"

```Prolog
mother(ann,henry)         :- write('[M1]'),nl.
mother(ann,mary)          :- write('[M2]'),nl.
mother(jane,mark)         :- write('[M3]'),nl.
mother(jane,francis)      :- write('[M4]'),nl.
mother(annette,jonathan)  :- write('[M5]'),nl.
mother(mary,bill)         :- write('[M6]'),nl.
mother(janice,louise)     :- write('[M7]'),nl.
mother(lucy,janet)        :- write('[M8]'),nl.
mother(louise,caroline)   :- write('[M9]'),nl.
mother(louise,martin)     :- write('[M10]'),nl.

father(henry,jonathan)    :- write('[F1]'),nl.
father(john,mary)         :- write('[F2]'),nl.
father(francis,william)   :- write('[F3]'),nl.
father(francis,louise)    :- write('[F4]'),nl.
father(john,mark)         :- write('[F5]'),nl.
father(gavin,lucy)        :- write('[F6]'),nl.
father(john,francis)      :- write('[F7]'),nl.
father(martin,david)      :- write('[F8]'),nl.
father(martin,janet)      :- write('[F9]'),nl.

parent(victoria,george)   :- write('[P1]'),nl.
parent(victoria,edward)   :- write('[P2]'),nl.
parent(X,Y)               :- write('[P3]'),nl, write('mother?'),nl,mother(X,Y), write('mother!'),nl.
parent(A,B)               :- write('[P3]'),nl, write('father?'),nl,father(A,B), write('father!'),nl.
parent(elizabeth,charles) :- write('[P5]'),nl.
parent(elizabeth,andrew)  :- write('[P6]'),nl.
```

```Prolog
?-parent(john,Child),write('The child is '),write(Child),nl.
[P3]
mother?
[P3]
father?
[F2]
father!
The child is mary
Child = mary
[F5]
father!
The child is mark
Child = mark
[F7]
father!
The child is francis
Child = francis
```

add clauses:

```Prolog
rich(jane) :- write('[R1]'),nl.
rich(john) :- write('[R2]'),nl.
rich(gavin) :- write('[R3]'),nl.

rich_father(X,Y) :- write('[RF1]'),nl, rich(X),father(X,Y).
```

```Prolog
?-rich_father(A,B).
[RF1]
[R1]
[R2]
[F2]
A = john,
B = mary
[F5]
A = john,
B = mark
[F7]
A = john,
B = francis
[R3]
[F6]
A = gavin,
B = lucy
```

## 3.5 Satisfying Goals: A Summary

The process of evaluating a sequence of goals:

```
(1) Are there more goals?
[Y] (2) Evaluate next goal
[Succeeds *] goto (1)
[Fails] (3) Are there any previous goals?
        [Y] (4) Re-evaluate previous goal
            [Succeeds **] goto (1)
            [Fails] goto (3)
        [N] Sequence of goals fails
[N] Sequence of goals succeeds *

*  Some variables may have become bound
** Some variables may have become bound to other values (or unbound)
```

The process of evaluating a goal:

```
(1) Is predicate a BIP?
[Y] Goal is evaluated as predefined by system (may succeed or fail)
[N] (2) Are there more clauses in the database? *
[Y] (3) Can the goal be unified with head of next clause?
    [Y **] Evaluate body of clause (a sequence of goals) ***
        [Succeeds **] Goal succeeds **
        [Fails] goto (2)
    [N] goto (2)
[N] Goal fails

*   Evaluation: Start at top of database
Re-evaluation: Start after clause matched when goal last satisfied
**  Some variables may have become bound
*** If the clause is a fact there is no body, so the goal succeeds immediately
```

## 3.6 Removing Common Variables

> [!example] "Removing Common Variables"

```Prolog
/* goal */
mypred(tuesday,likes(Z,Y),X)

/* head */
mypred(X,Y,Z) :- pred2(X,Q),pred3(Q,Y,Z).
```

Before attempting to unify the goal and the head of the clause, it is first necessary to rewrite the clause to ensure that it has no variables in common with the goal.
To be precise, the clause must not have any variables in common with any of the goals in the sequence of which the goal currently under consideration is part.

Prolog automatically replaces variables X, Y and Z in the clause systematically by other variabels that do not appear in the sequence of goals (or elsewhere in the clause). example:

```Prolog
mypred(X1,Y1,Z1) :- pred2(X1,Q),pred3(Q,Y1,Z1).
```

## 3.7 A Note on Declarative Programming

*The order in which the caluses defining a predicate occur in the database* and *the other of the goals in the body of a rule* are of vital importance when evaluating a user's query.

It's part of the philosophy of logic programming that programs shoule be written to minimize the effect of these two factors as far as possible.
Programs that do so are called fully or partly **declarative**.

> [!example] "Declarative Programming"

```Prolog
dog(fido). dog(rover). dog(jane). dog(tom). dog(fred). dog(henry).
cat(bill). cat(steve). cat(mary). cat(harry).
large(rover). large(william). large(martin). large(tom). large(steve). large(jim). large(mike).

large_animal(X) :- dog(X),large(X).
large_animal(Z) :- cat(Z),large(Z).

?- large_animal(X).
X = rover
X = tom
X = steve
false
```

```Prolog
dog(fido). dog(rover). dog(jane). dog(tom). dog(fred). dog(henry).
cat(bill). cat(steve). cat(mary). cat(harry).
large(rover). large(william). large(martin). large(tom). large(steve). large(jim). large(mike).

/* diff: rearrange the clauses in the program */
large_animal(Z) :- cat(Z),large(Z).
large_animal(X) :- dog(X),large(X).

?- large_animal(X).
X = steve
X = rover
X = tom
false
```

```Prolog
dog(fido). dog(rover). dog(jane). dog(tom). dog(fred). dog(henry).
cat(bill). cat(steve). cat(mary). cat(harry).
large(rover). large(william). large(martin). large(tom). large(steve). large(jim). large(mike).

/* diff: rearrange the order of the goals in the bodies of rules */
large_animal(X) :- large(X),dog(X).
large_animal(Z) :- large(Z),cat(Z).

?- large_animal(X).
X = rover
X = tom
X = steve
false
```

```Prolog
test(X) :- X>0,write(positive),nl.
test(0) :- write(zero),nl.
test(X) :- write(negative),nl.
```

a more declarative way:

```Prolog
test(X) :- X>0,write(positive),nl.
test(0) :- write(zero),nl.
test(X) :- X<0,write(negative),nl.
```

## 3.8 Important Note on User-Controlled Backtracking

In some cases there are no more solutions to be found and if the user enters a semicolon character the system will simply reply `false.`.

In other cases the system will attempt to find an alternative solution even though no other meaningfull solution would be possible, such as find the larger of two numbers or combining the contents of two text files into a single file.
Often the effect of doing so will be to produce output that is mysterious or obviously wrong.
In some cases, the system will go into an infinite loop and/or crash as the available memory fills up.


# 4 Operators and Arithmetic

## 4.1 Operators

> [!example] "Operators"

```Prolog
?-op(150,xfy,likes).
?-op(150,xf,is_female).
?-op(150,xf,isa_cat).
?-op(150,xfy,owns).

john likes X:- X is_female, X owns Y, Y isa_cat.

is_female(mary).
owns(mary,fido).
isa_cat(fido).
```

- `op(150,xfy,likes)`: convert user-defined predicate `likes` to an operator.
- `150`: the operator precedence, an integer from 0 upwards. The lower the number is, the higher the precedence. **Operator precedence** values are used to determine the order in which operators will be applied when more than one is used in a term.
- `xfy`: atoms specify prefix/infix/postfix.

`xfx`, `xfy`, `yfx`: meaning the predicate is binary, and is to be converted to an **infix** operator.

`fx`, `fy`: meaning the predicate is unary, and is to be converted to an **prefix** operator.

`xf`, `yf`: meaning the predicate is unary, and is to be converted to an **postfix** operator.

```Prolog
?- john likes mary.
true.
?- john likes X.
X = mary.
?- X likes mary.
X = john.
?- X likes Y.
X = john,
Y = mary.
?- is_female(X).
X = mary.
```

relational operators comparing numerical values:

```Prolog
X > 4
Y < Z
A = B

>(X,4)
X > 4
```

## 4.2 Arithmetic

> [!example] is/2

```Prolog
X is 6*Y+Z-3.2+P-Q/4

?- X is 10.5+4.7*2.
X = 19.9

?- Y is 10,Z is Y+1.
Y = 10,
Z = 11

?- X is sqrt(36).
X = 6

?- X is 10,Y is -X-2.
X = 10,
Y = -12

?- X is 30,Y is 5,Z is X+Y+X*Y.
X = 30,
Y = 5,
Z = 185.

?- X is 7,X is 6+1.
X = 7

?- 10 is 7+13-11+9.
false.
?- 18 is 7+13-11+9.
true.
```

> [!note] "Some arithmetic operators and arithmetic functions"

- `X + Y`: sum
- `X - Y`: difference
- `X * Y`: product
- `X / Y`: quotient
- `X // Y`: integer quotient
- `X mod Y`: remainder
- `X ^ Y`: power
- `-X`: negative
- `abs(X)`: absolute value
- `sin(X)`: sine
- `cos(X)`: cosine
- `max(X,Y)`: larger
- `round(X)`: round to the nearest integer
- `sqrt(X)`: square root

> [!note] "Unification in `is/2` operator"

- If the first argument is an unbound variable, it is bound to the value of the second argument (as a side effect) and the `is` goal succeeds.
- If the first argument is a number, or a bound variable with a numerical value, it is compared with the value of the second argument. If they are the same, the `is` goal succeeds, otherwise it fails.
- If the first argument is an atom, a compound term, a list, or a avaribale bound to one of these, the outcome is implementation-dependent.

> [!example] "'Assignment'"

`X is X + 1` is always fail, whether or not `X` is bound.

```Prolog
?- X is 10,X is X+1.
false.

/* Incorrect version */
increase(N) :- N is N+1.

?- increase(4).
false.

/*Correct version */
increase(N,M) :- M is N+1.

?- increase(4,X).
X = 5
```

> [!note] "Operator Precedence in Arithmetic Expressions"

Prolog gives each operator a numerical **precedence value**.

Operators with relatively high precedence such as `*` and `/` are applied before those with lower precedence such as `+` and `-`.
Operator with the same precedence (e.g. `+` and `-`, `*` and `/`) are applied from left to right.

> [!note] "Relational Operators"

The infix operators `=:=`, `=\=`, `>`, `>=`, `<`, `=<` are a special type known as **relational operators**.
They are used to compare the value of two arithmetic expressions.
Both arguments must be numbers, bound variables or arithmetic expressions.

```Prolog
?- 88+15-3 =:= 110-5*2.
true.

?- 100 =\= 99.
true.
```

## 4.3 Equality Operators

`E1 =:= E2` succeeds if the arithmetic expressions `E1` and `E2` evaluate to the same value.

> [!example] "Arithmetic Expression Equality `=:=`"

```Prolog
?- 6+4 =:= 6*3-8.
true.

?- sqrt(36)+4 =:= 5*11-45.
true.

checkeven(N) :- M is N//2,N =:= 2*M.

?- checkeven(12).
true.
?- checkeven(23).
false.
?- checkeven(-11).
false.
?- checkeven(-30).
true.
```

`E1 =\= E2` succeeds if the arithmetic expressions `E1` and `E2` do not evaluate to the same value.

> [!example] "Arithmetic Expression Inequality `=\=`"

```Prolog
?- 10 =\= 8+3.
true.
```

Both arguments of the infix operator `==` must be terms.
The goal `Term1 == Term2` succeeds if and only if `Term1` is identical to `Term2`.
Any variables used in the terms may or may not already be bound, but no variables are bound as a result of evaluating the goal.

> [!example] "Terms Identical `==`"

```Prolog
?- likes(X,prolog) == likes(X,prolog).
true.

?- likes(X,prolog) == likes(Y,prolog).
false.

?- X is 10,pred1(X) == pred1(10).
X = 10

?- X == 0.
false.

?- 6+4 == 3+7.
false.
```

The goal `Term1 \== Term2` succeeds if `Term1 == Term2` fails.

> [!example] "Terms Not Identical `\==`"

```Prolog
?- pred1(X) \== pred1(Y).
true.
```

The term equality operator `=` is similar to `==` with one vital difference.
The goal `Term1 = Term2` succeeds if terms `Term1` and `Term2` **unify**, i.e. there is some way of binding variables to values which would make the terms identical.
If the goal succeeds, such binding actually take place.

> [!example] "Terms Identical With Unification `=`"

```Prolog
?- pred1(X) = pred1(10).
X = 10

?- likes(X,prolog) = likes(john,Y).
X = john ,
Y = prolog

?- X = 0,X =:= 0.
X = 0

?- 6+4 = 3+7.
false.

?- 6+X = 6+3.
X = 3

?- likes(X,prolog) = likes(Y,prolog).
X = Y.

?- likes(X,prolog) = likes(Y,ada).
false.
```

The goal `Term1 \= Term2` succeeds if `Term1 = Term2` fails.

> [!example] "Non-Unification Between Two Terms `\=`"

```Prolog
?- 6+4 \= 3+7.
true.

?- likes(X,prolog) \= likes(john,Y).
false.

?- likes(X,prolog) \= likes(X,ada).
true.
```

## 4.4 Logical Operators

> [!example] "The `not` Operator"

```Prolog
?-op(1000,fy,not).

dog(fido).

?- not dog(fido).
false.
?- dog(fred).
false.
?- not dog(fred).
true.
?- X=0,X is 0.
X = 0
?- X=0,not X is 0.
false.
```

The goal `Goal1;Goal2` succeeds if either `Goal1` or `Goal2` succeeds.

> [!example] "The Disjunction Operator `;/2`"

```Prolog
?- 6<3; 7 is 5+2.
true.

?- 6*6 =:= 36; 10=8+3.
true.
```

## 4.5 More About Operator Precedence

> [!note] "Operator Precedence"

```
Precedence   Type    Operator(s)
1100         xfy     ;
1000         fy      not
700          xfx     is < > =< >= =:= =\= = \= == \==
500          yfx     + -
400          yfx     * / //
200          xfy     ^
200          fy      + -
```

- A term enclosed in parentheses has precedence zero.
- The precedence of a term is zero, unless its principal functor is an operator.
- The precedence of a term for which the principal functor is an operator is the precedence of the operator.

The difference between `x` and `y` in `Type`:
 
- `x` denotes an argument that has a precedence strictly lower than that of the operator.
- `y` denotes an argument that has a precedence less than or equal to that of the operator.

```Prolog
?-op(150,fx,not).
dog(fido).

?-dog(fido).
true
?-not dog(fido).
false
?-not not dog(fido).
Syntax error: Operator priority clash
```

```Prolog
?-op(150,fy,not).
dog(fido).

?-not not dog(fido).
true
```


# 5 Input and Output

## 5.1 Introduction

Like many other built-in predicates, those for input and output described in this chapter are all **unresatisfiable**, i.e. they always fail when backtracking.

## 5.2 Outputting Terms

> [!note] write/1`, `nl/0`, `writeq/1

The `write/1` predicate takes a single argument, which must be a valid Prolog term.
Evaluating the predicate causes the term to be written to the **current output stream**, which by default is the user's screen.

The built-in precidate `nl/0` takes no arguments.
Evaluating a `nl` goal causes a new line to be output to the current output stream.

The `writeq/1` predicate is identical to `write/1` except that atoms that need quotes for input are output between quotes (other atoms are not).

```Prolog
?- write(26),nl.
26
true.

?- write('a string of characters'),nl.
a string of characters
true.

?- write([a,b,c,d,[x,y,z]]),nl.
[a,b,c,d,[x,y,z]]
true.

?- write(mypred(a,b,c)),nl.
mypred(a,b,c)
true.

?- write('Example of use of nl'),nl,nl,write('end of example'),nl.
Example of use of nl
end of example
true.

/* writeq/1 */
?- writeq('a string of characters'),nl.
'a string of characters'
true.

?-writeq(dog),nl.
dog
true.

?- writeq('dog'),nl.
dog
true.
```

## 5.3 Inputting Terms

> [!note] read/1

The build-in predicate `read/1` is provided to input terms, it takes a single argument, which must be a variable.
Evaluating it causes the next term to be read from the **current input stream**, which by default is the user's keyboard.
In the input stream, the term must be followed by a dot `.` and at least one white space character, such as space or newline.
The dot and white space characters are read in but are not considered part of the term.

If the argument variable is already bound, the goal succeeds if and only if the input term is identical to the previously bound value.

```Prolog
?- read(X).
|:jim.
X = jim

?- read(X).
|:26.
X = 26

?- read(X).
|:mypred(a,b,c).
X = mypred(a,b,c)

?- read(Z).
|: [a,b,mypred(p,q,r),[z,y,x]].
Z = [a,b,mypred(p,q,r),[z,y,x]]

?- read(Y).
|: 'a string of characters'.
Y = 'a string of characters'

?- X = fred,read(X).
|:jim.
false.
?- X = fred,read(X).
|:fred.
X = fred
```

- `|:`: a prompt to indicate that user input is required.

## 5.4 Input and Output Using Characters

All printing characters and many non-printing characters have a corresponding ASCII value, which is an integer from 0 to 255.

## 5.5 Outputting Characters

> [!note] put/1

The built-in predicate `put/1` takes a single argument, which must be a number from 0 to 255 or an expression that evaluates to an integer in taht range.
Evaluating a `put` goal causes a single character to be output to the current output stream.
This is the character corresponding to the numerical value of its argument.

```Prolog
?- put(97),nl.
a
true.

?- put(122),nl.
z
true.

?- put(64),nl.
@
true.
```

## 5.6 Inputting Characters

> [!note] get0`, `get

The `get0` predicate takes a single argument, which must be a variable.
Evaluating a `get0` goal causes **a character** to read from the current input stream.
The varibale is then unified with the ASCII value of this character.

The `get` predicate takes a single argument, which must be a variable.
Evaluating a `get` goal causes **the next non-white-space character** to be read from the current input stream.
The variable is then unified with the ASCII value of this character.

```Prolog
?- get0(N).
|: a
N = 97
?- get0(N).
|: Z
N = 90
?- get0(M)
|:)
M = 41

?- M is 41,get0(M).
|:)
M = 41
?- M is 50,get0(M).
|:)
false.

?- get(X).
|: Z
X = 90
?- get(M).
|:     Z
M = 90
```

## 5.7 Using Characters: Examples

> [!example] "Using Characters"

- read in a series of characters from the keyboard finishing with * and to output their corresponding ASCII values one per line

```Prolog
readin :- get0(X),process(X).
process(42).
process(X) :- X =\= 42,write(X),nl,readin.

?- readin.
|: Prolog Example*
80
114
111
108
111
103
32
69
120
97
109
112
108
101
true.
```

- output the number of characters (excluding the *)

```Prolog
go(Total) :- count(0,Total).

count(Oldcount,Result) :-
  get0(X),process(X,Oldcount,Result).

process(42,Oldcount,Oldcount).
process(X,Oldcount,Result) :-
  X =\= 42,New is Oldcount + 1,count(New,Result).

?- go(T).
|: The time has come the walrus said*
T = 33
?- go(T)
|:*
T = 0
```

- read in a series of characters ending with * and count the number of vowels

```Prolog
go(Vowels) :- count(0,Vowels).

count(Oldvowels,Totvowels) :-
  get0(X),process(X,Oldvowels,Totvowels).

process(42,Oldvowels,Oldvowels).
process(X,Oldvowels,Totalvowels):-
  X =\= 42,processChar(X,Oldvowels,New),
  count(New,Totalvowels).

processChar(X,Oldvowels,New) :- vowel(X),
  New is Oldvowels + 1.
processChar(X,Oldvowels,Oldvowels).

vowel(65)./* A */
vowel(69)./* E */
vowel(73)./* I */
vowel(79)./* O */
vowel(85)./* U */
vowel(97)./* a */
vowel(101)./* e */
vowel(105)./* i */
vowel(111)./* o */
vowel(117)./* u */

?- go(Vowels).
|: In the beginning was the word*
Vowels = 8
?- go(Vowels).
|: pqrst*
Vowels = 0
```

## 5.8 Input and Output Using Files

The user may open and close input and output stream associated with any number of named files
but there can only be one current input stream and one current output stream at any time.
Note that no file can be open for both input and output at the same time (except `user`), 
and the `user` input and output streams cannot be closed.

## 5.9 File Output: Changing the Current Output Stream

> [!note] tell/1`, `told/0`, `telling/1

The `tell/1` predicate takes a single argument, which is an atom or variable representing a file name, e.g. `tell('outfile.txt')`.
Evaluating a `tell` goal causes the named file to become the current output stream.
If the file is not already open, a file with the specified name is first created.
The file corresponding to the previous current output stream remains open when a new current output stream is selected.
Only the current output stream can be closed.

The default current output stream is `user`, i.e. the user's terminal.
This value can be restored either by using `told` or by `tell(user)`.

The `told/0` predicate takes no arguments.
Evaluating a `told` goal causes the current output file to be closed and the current output stream to be reset to `user`.

The `telling/1` takes one argument, which must be a variable and will normally be unbounded.
Evaluating a `telling` goal causes the variable to be bound to the name of the current output stream.

## 5.10 File Input: Changing the Current Input Stream

> [!note] see/1`, `seen/0`, `seeing/1

The `see/1` predicate takes a single argument, which is an atom or variable representing a file name, e.g. `see('myfile.txt')`.
Evaluating a `see` goal causes the named file to become the current input stream.
If the file is not already open it is first opened (for read access only).
If it is not possible to open a file with the given name, an error will be generated.
The file corresponding to the previous current input stream remains open when a new current input stream is selected.
Only the current input stream can be closed.

The default current input stream is `user`, i.e. the user's terminal.
This value can be restored either by using `seen` or by `see(user)`.

The `seen/0` predicate takes no arguments.
Evaluating a `seen` goal causes the current input file to be closed and the current input stream to be reset to `user`.

The `seeing/1` takes one argument, which must be a variable and will normally be unbounded.
Evaluating a `seeing` goal causes the variable to be bound to the name of the current input stream.


### 5.10.1 Reading from Files: End of File

If the end of file is encountered,

- when evaluating the goal `read(X)`, variable `X` will be bound to the atom `end_of_file`.
- when evaluating the goal `get(X)` or `get0(X)`, variable `X` will be bound to a 'special' numerical value, this will typically be -1, but may vary from implementations of Prolog.

### 5.10.2 Reading from Files: End of Record

The end of a line of input at the user's terminal and the end of a record in a file will typically both be indicated by the ASCII value 10. 
In some Prolog systems, different values are used.
This is the assumption we will make in this book.

## 5.11 Using Files: Examples

> [!example] "Using Files"

- read the characters in a text file myfile.txt until a * character is reached and output the number of vowels

```Prolog
go(Vowels):-see('myfile.txt'),count(0,Vowels),seen.

count(Oldvowels,Totvowels) :-
  get0(X),process(X,Oldvowels,Totvowels).

process(42,Oldvowels,Oldvowels).
process(X,Oldvowels,Totalvowels):-
  X =\= 42,processChar(X,Oldvowels,New),
  count(New,Totalvowels).

processChar(X,Oldvowels,New) :- vowel(X),
  New is Oldvowels + 1.
processChar(X,Oldvowels,Oldvowels).

vowel(65)./* A */
vowel(69)./* E */
vowel(73)./* I */
vowel(79)./* O */
vowel(85)./* U */
vowel(97)./* a */
vowel(101)./* e */
vowel(105)./* i */
vowel(111)./* o */
vowel(117)./* u */
```

- read the first four terms from a specified file and output them to another specified file, one per line

```text title="textfile.txt"
'first term'. 'second term'.
'third term'.
'fourth term'. 'fifth term'.
```

```Prolog
readterms(Infile,Outfile):-
  seeing(S),
  see(Infile),
  telling(T),
  tell(Outfile),  read(T1),write(T1),nl,read(T2),write(T2),nl,
  read(T3),write(T3),nl,read(T4),write(T4),nl,  seen,
  see(S),
  told,
  tell(T).

?- readterms('textfile.txt','outfile.txt').
true.
```

```shell
$ cat outfile.txt
first term
second term
third term
fourth term
```

It is a good programming practice to restore the original input and output streams as the final steps when a goal such as `readterms` is evaluated.

- copy characters input (as a single line) at the user's terminal to a specified file, until the character ! is entered

```Prolog
copychars(Outfile) :- 
  telling(T),
  tell(Outfile),

  copy_characters,  told,
  tell(T).copy_characters :- get0(N),process(N).

/* 33 is ASCII value of character ! */
process(33).
process(N) :- N =\= 33,put(N),copy_characters.
    
?- copychars('myfile.txt').
|: abxyz!
true.
```

# 6 Loops

## 6.1 Introduction

Prolog has no looping facilities, similar effects can be obtained that enable a sequence of goals to be evaluated repreatedly.
This can be done in a variety of ways, using *backtracking*, *recursion*, *built-in predicates*, or a combination of these.

## 6.2 Looping a Fixed Number of Times

> [!example] "Looping a Fixed Number of Times"

(1) output integers from a specified value down to 1

```Prolog
loop(0).
loop(N) :- N>0,write('The value is: '),write(N),nl,
    M is N-1,loop(M).

?- loop(6).
The value is: 6
The value is: 5
The value is: 4
The value is: 3
The value is: 2
The value is: 1
true.
```

(2) output integer from First to Last inclusive

```Prolog
output_values(Last,Last) :- write(Last),nl,
    write('end of example'),nl.
output_values(First,Last) :- First =\= Last,write(First),nl,
    N is First + 1,output_values(N,Last).

?- output_values(5,12).
5
6
7
8
9
10
11
12
end of example
true.
```

(3) find the sum of the integers from 1 to N (say for N = 100).

```Prolog
sumto(1,1).
sumto(N,S) :- N>1,N1 is N-1,sumto(N1,S1),S is S1 + N.

?- sumto(100,N).
N = 5050
?- sumto(1,1).
true.
```

(4) output the squares of the first N integers, one per line

```Prolog
writesquares(1) :- write(1),nl.
writesquares(N) :- N>1,N1 is N-1,writesquares(N1),
    Nsq is N*N,write(Nsq),nl.

?- writesquares(6).
1
4
9
16
25
36
true
```

(5) read the first 6 terms from a specified file and write them to the current output stream

```Prolog
read_six(Infile) :- 
    seeing(S),
    see(Infile),
    
    process_terms(6),
    
    seen,
    see(S).

process_terms(0).
process_terms(N) :- N>0,read(X),write(X),nl,N1 is N-1,
    process_terms(N1).
```

## 6.3 Looping Until a Condition Is Satisfied

No 'until loop' is available directly in Prolog, but a similar effect can be obtained in several ways.

### 6.3.1 Recursion

> [!example] "Recursion"

(1) read terms entered by the user from the keyboard and output them to the screen, until `end` is encountered

```Prolog
go:-loop(start). /* start is a dummy value used to get the looping process started.*/

loop(end).
loop(X) :- X \= end,write('Type end to end: '),read(Word),
    write('Input was '),write(Word),nl,loop(Word).

?- go.
Type end to end: university.
Input was university
Type end to end: of.
Input was of
Type end to end: portsmouth.
Input was portsmouth
Type end to end: end.
Input was end
true.
```

(2) repeatedly prompts the user to enter a term until either `yes` or `no` is entered

```Prolog
get_answer(Ans) :- write('Enter answer to question'),
    nl,get_answer2(Ans).

get_answer2(Ans) :-
    write('answer yes or no: '),
    read(A),
    ((valid(A),AnsDA,write('Answer is '),write(A),nl)
     ;
    get_answer2(Ans)).

valid(yes).
valid(no).

?- get_answer(Myanswer).
Enter answer to question
answer yes or no: maybe.
answer yes or no: possibly.
answer yes or no: yes.
Answer is yes
Myanswer = yes
```

### 6.3.2 Using the `repeat` Predicate

The goal `repeat` does not repeat anything, it merely succeeds whenever it is called.
It also succeeds on backtracking. The effect of this is to change the order of evaluating goals from 'right to left' back to 'left to right'.

> [!example] repeat

```Prolog
get_answer(Ans):-
    write('Enter answer to question'),nl,
    repeat,
    write('answer yes or no: '),read(Ans),
    valid(Ans),write('Answer is '),write(Ans),nl.

valid(yes). valid(no).
```

- The first five goals in the body of `get_answer` will always succeed.
- Evaluting the fifth goal `read(Ans)` will prompt the user to enter a term.
- If the term input is anything but `yes` or `no`, say `unsure`, the following goal `valid(Ans)` will fail. Prolog will then backtrack over `read(Ans)` and `write('answer yes or no: ')`, both of which are unresatisfiable, i.e. will always fail on backtracking.
- Backtracking will then reach the predicate `repeat` and succeed, causing evaluationg to proceed from left to right again, with `write('answer yes or no: ')` and `read(Ans)` both succeeding, followed by a further evaluation of `valid(Ans)`.
- Depending on the value `Ans`, i.e. the user's input, the `valid(Ans)` goal will either fail, in which case Prolog will backtrack as far as `repeat` as before, or it will succeed in which case the fianl thre goals `write('Answer is ')`, `write(Ans)` and `nl` will all succeed.
- The overall effect is that the two goals `write('answer yes or no: ')` and `read(Ans)` are called repeatedly until the terminating condition `valid(Ans)` is satisfied, effectively creating a loop between `repeat` and `valid(Ans)`.

```Prolog
?- get_answer(X).
Enter answer to question
answer yes or no: unsure.
answer yes or no: possibly.
answer yes or no: no.
answer is no
X = no
```

Gaols to the left of `repeat` in the body of a clause will never be reached on backtraking.

> [!example] "More `repeat` Examples"

reads a sequence of terms from a specified file and outputs them to the current output stream until the term `end` is encountered

```Prolog
readterms(Infile) :-
    seeing(S),see(Infile),
    repeat,
    read(X),write(X),nl,X=end,
    seen,see(S).
```

```text title="myfile.txt"
'first term'. 'second term'.
'third term'. 'fourth term'.
'fifth term'. 'sixth term'.
'seventh term'.
'eighth term'.
end.
```

```Prolog
?- readterms('myfile.txt').
first term
second term
third term
fourth term
fifth term
sixth term
seventh term
eighth term
end
true.
```

> [!example] "A menu structure loops back repeatedly to request more input"

```Prolog
go:- write('This shows how a repeated menu works'),
    menu.

menu:-nl,write('MENU'),nl,
    write('a. Activity A'),nl,write('b. Activity B'),nl,
    write('c. Activity C'),nl,write('d. End'),nl,
    read(Choice),nl,choice(Choice).

choice(a):-write('Activity A chosen'),menu.
choice(b):-write('Activity B chosen'),menu.
choice(c):-write('Activity C chosen'),menu.
choice(d):-write('Goodbye!'),nl.
choice(_):-write('Please try again!'),menu.
```

```Prolog
?- go.
This shows how a repeated menu works
MENU
a. Activity A
b. Activity B
c. Activity C
d. End
: b.
Activity B chosen
MENU
a. Activity A
b. Activity B
c. Activity C
d. End
: xxx.
Please try again!
MENU
a. Activity A
b. Activity B
c. Activity C
d. End
: d.
Goodbye!
true.
```

## 6.4 Backtracking with Failure

> [!note] fail

The predicate `fail` always fails, whether on standard evaluation left to right or on backtracking.

When `fail` is combined with Prolog's automatic backtracking, we can search through the data base to find all the clauses with a specified property.

### 6.4.1 Searching the Prolog Database

> [!example] fail

```Prolog
dog(fido).
dog(fred).
dog(jonathan).

alldogs :- dog(X),write(X),write(' is a dog'),nl,fail.
alldogs.

?- alldogs.
fido is a dog
fred is a dog
jonathan is a dog
true.
```

- Calling `alldogs` will cause `dog(X)` to be matched with the `dog` clause in the database.
- Initially `X` will be bound to `fido` and 'fido is a dog' will be output.
- The final goal in the first clause of the `alldogs` predicate will then cause evaluation to fail.
- Prolog will then backtrack over `nl` and the two `write` goals until it reaches `dog(X)`. This goal will succeed for a second time causing `X` to be bound to `fred`.
- This process will continue until `fido`, `fred` and `jonathan` have all been output, when evaluation will again fail.
- This time the call to `dog(X)` will also fail as there are no further `dog` clauses in the database. This will cause the first clause for `alldogs` to fail and Prolog to examine the second clause of `alldogs`. This will succeed and evaluation will stop.

```Prolog
person(john,smith,45,london,doctor).
person(martin,williams,33,birmingham,teacher).
person(henry,smith,26,manchester,plumber).
person(jane,wilson,62,london,teacher).
person(mary,smith,29,glasgow,surveyor).

/* find the names of all the teachers */
allteachers :- person(Forename,Surname,_,_,teacher),
    write(Forename),write(' '),write(Surname),nl,
    fail.
allteachers.

?- allteachers.
martin williams
jane wilson
true.

/* find all the people in the database given previously, down to williams, 
using only standard backtracking */
somepeople :- person(Forename,Surname,_,_,_),
    write(Forename),write(' '),write(Surname),nl,
    Surname=williams.
somepeople.

?- somepeople.
john smith
martin williams
true.
```

### 6.4.2 Finding Multiple Solutions

Backtracking with failure can also be used to find all the ways of satisfying a goal.

> [!example] findrout(Town1,Town2,Route)

find all possible routes between `Town1` and `Town2`, and write out each one on a seperate line:

```Prolog
find_all_routes(Town1,Town2):-
    findroute(Town1,Town2,Route),
    write('Possible route: '),write(Route),nl,fail.

find_all_routes(_,_).
```

- `Town1`, `Town2` are atoms and `Route` is a list.
 

# 7 Preventing Backtracking

## 7.1 Introduction

This chapter is about preventing the Prolog system from backtracking using a built-in predicate called `cut`, which is written as an exclamation mark character `!`.
The best advice is probably to use it only sparingly and with care.

## 7.2 The Cut Predicate

> [!example] larger/3`, `sumto/2

- `larger(A,B,C)`: takes the value of the larger of its first two arguments (which are assumed to be numbers) and returns it as the value of the third
- `sumto(N,S)`: causes the sum of the integers from 1 to `N` to be calculated and returns the answer as the value of `S` 

```Prolog
larger(A,B,A) :- A > B.
larger(A,B,B).

?- larger(8,6,X).
X = 8

/* force the system to backtrack, 
it will go on to examine the second clause */
?- larger(8,6,X).
X = 8;
X = 6
```

```Prolog
sumto(1,1).
sumto(N,S) :- N1 is N-1,sumto(N1,S1),
    S is S1+N.

?- sumto(3,S).
S = 6
/* force backtracking will cause the system to crash, 
such as 'stack overflow':
sumto(1,S)
sumto(0,S)
sumto(-1,S1)
sumto(-2,S1)
...
*/
```

correction:

```Prolog
larger(A,B,A) :- A > B.
larger(A,B,B) :- A =< B.

sumto(1,1).
sumto(N,S) :- N>1,N1 is N-1,sumto(N1,S1),S is S1+N.
```

A more general way to avoid unwanted backtracking is to use a **cut**.

> [!note] !

The goal `!` in the body of a rule always succeeds when first evaluated.
On backtracking, it always fails and prevents any further evaluation of the current goal, which therefore fails.

> [!example] "`larger/3`, `sumto/2` revised with cut"

```Prolog
larger(A,B,A) :- A > B,!.
larger(A,B,B).

?- larger(8,6,X).
X = 8
?-

sumto(1,1) :- !.
sumto(N,S):-N1 is N-1,sumto(N1,S1),
    S is S1+N.

?- sumto(6,S).
S = 21
?-
```

> [!example] "classify a number as positive, negative or zero"

```Prolog
classify(0,zero).
classify(N,negative) :- N<0.
classify(N,positive).

?- classify(0,N).
N = zero;
N = positive

?- classify(-4,X).
X = negative;
X = positive
?-
```

```Prolog
classify(0,zero).
classify(N,negative) :- N<0.
classify(N,positive) :- N>0.

classify(0,zero) :- !.
classify(N,negative) :- N<0,!.
classify(N,positive).

?- classify(0,N).
N = zero
?- classify(-4,N).
N = negative
?-
```

> [!example] "prompt the user for an answer to a question until a valid answer is entered."

```Prolog
get_answer(Ans) :-
    write('Enter answer to question'),nl,
    repeat,
    write('answer yes or no: '),read(Ans),
    valid(Ans),write('Answer is '),write(Ans),nl.

valid(yes).
valid(no).

?- get_answer(X).
Enter answer to question
answer yes or no: maybe.
answer yes or no: yes.
Answer is yes
X = yes;
answer yes or no: no.
Answer is no
X = no;
answer yes or no: unsure.
answer yes or no: yes.
Answer is yes
X = yes
...
```

```Prolog
get_answer(Ans) :-
    write('Enter answer to question'),nl.
    repeat,
    write('answer yes or no: '),read(Ans),
    valid(Ans),write('Answer is '),write(Ans),nl,
    !.

valid(yes).
valid(no).

?- get_answer(X).
Enter answer to question
answer yes or no: maybe.
answer yes or no: unsure.
answer yes or no: yes.
Answer is yes
X = yes
?-
```

It is assumed that the user presses the 'return' key to suppress backtracking.

> [!example] "prompt the user for input until a positive number is entered"

```Prolog
classify(0,zero).
classify(N,negative) :- N<0.
classify(N,positive).

go :- write(start),nl,
    repeat,write('enter a positive value'),read(N),
    classify(N,Type),TypeDpositive,
    write('positive value is '),write(N),nl.

?- go.
start
enter a positive value: 28.
positive value is 28
true.

?- go.
start
enter a positive value: -6.
positive value is -6
true.

?- go.
start
enter a positive value: 0.
```

```Prolog
classify(0,zero) :- !.
classify(N,negative) :- N<0,!.
classify(N,positive).

go:-write(start),nl,
    repeat,
    write('enter a positive value: '),read(N),
    classify(N,Type),
    TypeDpositive,
    write('positive value is '),write(N),nl,
    !.

?- go.
start
enter a positive value: -6.
enter a positive value: -7.
enter a positive value: 0.
enter a positive value: 45.
positive value is 45
true.
```

## 7.3 Cut with Failure

Another use of cut that can sometimes be helpful is to specify exceptions to general rules.

The combination of goals `!` and `fail` is known as **cut with failure**.

> [!example] "cut with failure"

```Prolog
bird(sparrow).
bird(eagle).
bird(duck).
bird(crow).
bird(ostrich).
bird(puffin).
bird(swan).
bird(albatross).
bird(starling).
bird(owl).
bird(kingfisher).
bird(thrush).
```

```Prolog
can_fly(ostrich) :- fail.
can_fly(X) :- bird(X).

?- can_fly(duck).
true.
?- can_fly(ostrich).
true.
```

```Prolog
can_fly(ostrich) :- !,fail.
can_fly(X) :- bird(X).

?- can_fly(duck).
true.
?- can_fly(ostrich).
false.
```


# 8 Changing the Prolog Database

## 8.1 Changing the Database: Adding and Deleting Clauses

The normal way of placing clauses in the Prolog database is to `consult` a file.
This causes all the clauses in the file to be loaded into the database. 
Any existing clauses for the same predicates are first deleted.

Prolog also has built-in predicates for adding clauses to and deleting clauses from the database which can be useful for more advanced programming in the language.
These built-in predicated can be used either in the body of a rule or as directives entered at the system prompt.

If one or more clauses for predicates are loaded into the database from a program file using `consult/1`, and we want to add clauses or remove predicates, we should first tell the system to treat the predicates dynamic, e.g. `?-dynamic(mypred/3).`

## 8.2 Adding Clauses

> [!note] assertz(Clause)

The predicate `assertz/1` causes `Clause` to be added to the database at the **end** of the sequence of clauses that define the corresponding predicate.

The clause used for the first argument should be written without a terminationg full stop.
Rules must be enclosed in an additional pair of parentheses.
The clause may include one or more variables.
    
```Prolog
?-assertz(dog(fido)).
?-assertz((go:-write('hello world'),nl)).

?-assertz(dog(X)).
?-assertz((go(X):-write('hello'),write(X),nl)).
```

> [!note] asserta(Clause)

The predicate `asserta/1` causes `Clause` to be added to the database at the **start** of the sequence of clauses that define the corresponding predicate.

The clause used for the first argument should be written without a terminationg full stop.
Rules must be enclosed in an additional pair of parentheses.

```Prolog
?-asserta(dog(fido)).
?-asserta((go:-write('hello world'),nl)).
```

## 8.3 Deleting Clauses

> [!note] retract(Clause)

The predicate `retract/1` takes a single argument, which must be a clause, i.e. a fact or a rule.
It causes the first clause in the database that matches (i.e. unifies with) `Clause` to be deleted.

```Prolog
?-dynamic(dog/1).
dog(jim).    /* (1) */
dog(fido).   /* (2) */
dog(henry).  /* (3) */
dog(X).      /* (4) */

?-retract(dog(fido)). /* delete (2) */
?-retract(dog(X)).    /* delete (1) */
```

> [!note] retractall(Head)

The predicate `retractall/1` takes a single argument which must be the head of a clause.
It causes every clause in the database whoes head matches `Head` to be delete.
It always succeeds even if no clauses are deleted.

```Prolog
/* deletes all the clauses for the mypred/3 predicate */
?-retractall(mypred(_,_,_)).

/* deletes all clauses for the parent/2 predicate 
which have the atom john as their first argument*/
?-retractall(parent(john,Y)).

/* only removes the clauses for predicate mypred/0, 
i.e. the atom mypred*/
?-retractall(mypred).
```

## 8.4 Changing the Database: Example

> [!example] "Changing the Database"

```Prolog
?- assertz(mypred(first)).
true.
?- assertz(mypred(second)).
true.
?- assertz(mypred(third)).
true.
?- assertz(mypred(fourth)).
true.

?- listing(mypred).
mypred(first).
mypred(second).
mypred(third).
mypred(fourth).
true.

?- asserta(mypred(new1)).
true.
?- listing(mypred).
mypred(new1).
mypred(first).
mypred(second).
mypred(third).
mypred(fourth).
true.

?- assertz(mypred(new2)).
true.
?- listing(mypred).
mypred(new1).
mypred(first).
mypred(second).
mypred(third).
mypred(fourth).
mypred(new2).
true.

?- mypred(X).
X = new1 ;
X = first ;
X = second ;
X = third ;
X = fourth ;
X = new2

?- retract(mypred(first)).
true.
?- listing(mypred).
mypred(new1).
mypred(second).
mypred(third).
mypred(fourth).
mypred(new2).
true.

?- retractall(mypred(_)).
true.
?- listing(mypred).
true.
```

## 8.5 Maintaining a Database of Facts

The predicates `assertz`, `retract` etc. can be used to create and maintain a database of related facts within the full Prolog database of facts and rules.

> [!example] "Maintaining a Database of Facts"

```text title="people.txt"
john. smith. 45. london. doctor.
martin. williams. 33. birmingham. teacher.
henry. smith. 26. manchester. plumber.
jane. wilson. 62. london. teacher.
mary. smith. 29. glasgow. surveyor.
end.
```

```Prolog
/* Creating a Database */
setup :- seeing(S),see('people.txt'),
    read_data,
    write('Data read'),nl,
    seen,see(S).

read_data:-
    read(A),process(A).

process(end).
process(A):-
    read(B),read(C),read(D),read(E),
    assertz(person(A,B,C,D,E)),read_data.

/* Removing a Clause */
remove(Forename,Surname) :-
    retract(person(Forename,Surname,_,_,_)).

/* Changing a Clause */
change(Forename,Surname,New_Profession) :-
    person(Forename,Surname,Age,City,Profession),
    retract(person(Forename,Surname,Age,City,Profession)),
    assertz(person(Forename,Surname,Age,City,New_Profession)).

/* Outputting the Database to a File */
output_data :-
    telling(T),tell('people2.txt'),
    write_data,
    told,tell(T),
    write('Data written'),nl.

write_data :- person(A,B,C,D,E),
    write(A),write('. '),
    write(B),write('. '),
    write(C),write('. '),
    write(D),write('. '),
    write(E),write('.'),nl,
    fail.
write_data :- write('end.'),nl.
```

- Creating a Database

```Prolog
/* example: person(john,smith,45,london,doctor). */
?- setup.
Data read
true.

?- listing(person).
person( john, smith, 45, london, doctor ).
person( martin, williams, 33, birmingham, teacher ).
person( henry, smith, 26, manchester, plumber ).
person( jane, wilson, 62, london, teacher ).
person( mary, smith, 29, glasgow, surveyor ).
true.
```

- Removing a Clause

```Prolog
?- remove(henry,smith).
true.
?- listing(person).
person( john, smith, 45, london, doctor ).
person( martin, williams, 33, birmingham, teacher ).
person( jane, wilson, 62, london, teacher ).
person( mary, smith, 29, glasgow, surveyor ).
true.
```

- Changing a Clause

```Prolog
?- change(jane,wilson,architect).
true.
?- listing(person).
person( john, smith, 45, london, doctor ).
person( martin, williams, 33, birmingham, teacher ).
person( mary, smith, 29, glasgow, surveyor ).
person( jane, wilson, 62, london, architect ).
true.
```

- Outputting the Database to a File

```Prolog
?- output_data.
Data written
true.
```


# 9 List Processing

## 9.1 Representing Data as Lists

A **list** is written as a sequence of values, known as *list elements*, seperated by commas and enclosed in square brackets, e.g. `[dog,cat,fish,man]`. 
We call this 'standard bracketed notation'.
A list element can be any Prolog term, including a bound or unbound variable or another list.
A list element that is itself a list is known as a **sublist**.
The list with no elements is known as the **empty list** and is written as `[]`.

For non-empty lists, the first element is known as the **head**, the list remaining after the first element is removed is called the **tail**.
For example, the head of the list `[dog,cat,fish,man]` is the atom `dog` and the tail is the list `[cat,fish,man]`.

## 9.2 Notation for Lists

An alternative way of representing a list is provided by the 'cons' notation (list constructor).
A list is represented by the notation `[elements | list]`.
The `elements` part is a sequence of one or more list elements, which may be any Prolog terms.
The `list` part represents a list.
The list `[elements | list]` is an augmented version of the list `list` with the sequence of elements indicated by `elements` inserted before any elements that are already there. e.g. `[one|[two,three]]` represents `[one,two,three]`.

The cons notation for a list can be used anywhere the standard bracketed form would be valid.

> [!example] "cons notation for lists"

```Prolog
?- write([alpha|[beta,gamma,delta]]),nl.
[alpha,beta,gamma,delta]
true.
?- write([alpha,beta,gamma|[delta]]),nl.
[alpha,beta,gamma,delta]
true.
?- write([alpha,beta,gamma,delta|[]]),nl.
[alpha,beta,gamma,delta]
true.
?- write([alpha,beta|[gamma,delta]]),nl.
[alpha,beta,gamma,delta]
true.
?- write([alpha,beta|[gamma|[delta|[]]]]),nl.
[alpha,beta,gamma,delta]
true.

?- L=[red,blue,green,yellow],write([brown|L]),nl.
[brown,red,blue,green,yellow]

?- write('Type a list: '),read(L),L1=[start|L],write('New list is '),write(L1),nl.
Type a list: [[london,paris],[x,y,z],27].
New list is [start,[london,paris],[x,y,z],27]
```

## 9.3 Decomposing a List

Breaking a list into its head and tail is often done using the list constructor.

> [!example] "Decomposing a List"

```Prolog
/* write out the elements of a list, one per line */
writeall([]).
writeall([A|L]) :- write(A),nl,writeall(L).

?- writeall([alpha,'this is a string',20,[a,b,c]]).
alpha
this is a string
20
[a,b,c]
true.
```

- When a goal such as `writeall([a,b,c])` is evaluated, it is matched against (unified with) the head of the second clause of `writeall`: `writeall([A|L])`.
- The matching process causes `A` to be bound to atom `a` and `L` to be bound to list `[b,c]`.
- The recursive call to `writeall` with the tail of the original list `L`, as its argument is a standard programming technique used in list processing.
- As is frequently the case, the empty list is treated separately, in this case by the first clause of `writeall`.

Working with nested lists:

```Prolog
/* causes the names of all the cities that are located in England to be output */

write_english([]).
write_english([[City,england]|L]):-
    write(City),nl,
    write_english(L).
write_english([A|L]) :- write_english(L).

go:- write_english([[london,england],[paris,france],
    [berlin,germany],[portsmouth,england],
    [bristol,england],
    [edinburgh,scotland]]).

?- go.
london
portsmouth
bristol
true.
```

takes as its first argument a list of at least one element,
if the second argument is an unbound variable, it is bound to the same list with the first element replaced by the atom `first`

```Prolog
replace([A|L],[first|L]).

?- replace([1,2,3,4,5],L).
L = [first,2,3,4,5]
?- replace([[a,b,c],[d,e,f],[g,h,i]],L).
L = [first, [d,e,f],[g,h,i]]
```

## 9.4 Built-in Predicate: `member`

> [!note] member/2

The predicate `member` takes two arguments.

- If the first argument is any term except a variable and the second argument is a list, `member` succeeds if the first argument is a member of the list denoted by the second argument (i.e. one of its list elements).

```Prolog
?- member(a,[a,b,c]).
true.
?- member(mypred(a,b,c),[q,r,s,mypred(a,b,c),w]).
true.
?- member(x,[]).
false.
?- member([1,2,3],[a,b,[1,2,3],c]).
true.
```

- If the first argument is an unbound variable, it is bound to an element of the list working from left to right.

```Prolog
?- member(X,[a,b,c]).
X = a ;
X = b ;
X = c ;
false.

get_answer2(Ans) :- repeat,
    write('answer yes, no or maybe: '),read(Ans),
    member(Ans,[yes,no,maybe]),
    write('answer is '),write(Ans),nl,!.

?- get_answer2(X).
answer yes, no or maybe: possibly.
answer yes, no or maybe: unsure.
answer yes, no or maybe: maybe.
answer is maybe
X = maybe
```

## 9.5 Built-in Predicate: `length`

> [!note] length/2

The predicate `length` takes two arguments.
The first is a list.

- If the second is an unbound variable it is bound to the length to the length of the list, i.e. the number of elements it contains.

```Prolog
?- length([a,b,c,d],X).
X = 4
?- length([[a,b,c],[d,e,f],[g,h,i]],L).
L = 3
?- length([],L).
L = 0
```

- If the second argument is a number, or a variable bound to a number, its value is compared with the length of the list.

```Prolog
?- length([a,b,c],3).
true.
?- length([a,b,c],4).
false.
?- N is 3,length([a,b,c],N).
N = 3
```

## 9.6 Built-in Predicate: `reverse`

> [!note] reverse/2

The predicate `reverse` takes two arguments.

- If the first is a list and the second is an unbound variable (or vice versa), the variable will be bound to the value of the list with the elements written in reverse order.

```Prolog
?- reverse([1,2,3,4],L).
L = [4,3,2,1]
?- reverse(L,[1,2,3,4]).
L = [4,3,2,1]
?- reverse([[dog,cat],[1,2],[bird,mouse],[3,4,5,6]],L).
L = [[3,4,5,6],[bird,mouse],[1,2],[dog,cat]]
```

- If both arguments are lists, `reverse` succeeds if one is the reverse of the other.

```Prolog
?- reverse([1,2,3,4],[4,3,2,1]).
true.
?- reverse([1,2,3,4],[3,2,1]).
false.
```

```Prolog
/*
arg 1: a list
arg 2: 
    an unbounded variable: bound to the list with last element removed.
    a list: test whether same as the first list with the last element removed.
*/
front(L1,L2):-
    reverse(L1,L3),remove_head(L3,L4),reverse(L4,L2).
remove_head([A|L],L).

?- front([a,b,c],L).
L = [a,b]
?- front([[a,b,c],[d,e,f],[g,h,i]],L).
L = [[a,b,c],[d,e,f]]

?- front([a,b,c],[a,b]).
true.
?- front([[a,b,c],[d,e,f],[g,h,i]],[[a,b,c],[d,e,f]]).
true.
?- front([a,b,c,d],[a,b,d]).
false.
```

## 9.7 Built-in Predicate: `append`

The term **concatenating** two lists means creating a new list, the elements of which are those of the first list followed by those of the second list.
Concatenating `[a,b,c]` with `[p,q,r,s]` gives the list `[a,b,c,p,q,r,s]`.
Concatenating `[]` with `[x,y]` gives `[x,y]`.

> [!note] append/3

The predicate `append` takes three arguments.

- If the first two arguments are lists and the third argument is an unbound variable, the third argument is bound to a list comprising the first two lists concatenated.

```Prolog
?- append([1,2,3,4],[5,6,7,8,9],L).
L = [1,2,3,4,5,6,7,8,9]
?- append([],[1,2,3],L).
L = [1,2,3]
?- append([[a,b,c],d,e,f],[g,h,[i,j,k]],L).
L = [[a,b,c],d,e,f,g,h,[i,j,k]]
```

- If the first two arguments are variables and the third is a list, it can be used with backtracking to find all possible pairs of lists which when concatenated give the third argument.

```Prolog
?- append(L1,L2,[1,2,3,4,5]).
L1 = [] ,
L2 = [1,2,3,4,5] ;
L1 = [1] ,
L2 = [2,3,4,5] ;
L1 = [1,2] ,
L2 = [3,4,5] ;
L1 = [1,2,3] ,
L2 = [4,5] ;
L1 = [1,2,3,4] ,
L2 = [5] ;
L1 = [1,2,3,4,5] ,
L2 = [] ;
false.

?- append(X,[YjZ],[1,2,3,4,5,6]).
X = [] ,
Y = 1 ,
Z = [2,3,4,5,6] ;
X = [1] ,
Y = 2 ,
Z = [3,4,5,6] ;
X = [1,2] ,
Y = 3 ,
Z = [4,5,6] ;
X = [1,2,3] ,
Y = 4 ,
Z = [5,6] ;
X = [1,2,3,4] ,
Y = 5 ,
Z = [6] ;
X = [1,2,3,4,5] ,
Y = 6 ,
Z = [] ;
false.
```

## 9.8 List Processing: Examples

> [!example] "List Processing"

- `find_largest/2`: takes a list of numbers as its first argument and assigns the value of the largest element to its second argument (assumed to be an unbound variable)

assumed that the list contains at least one number

```Prolog
find_largest([X|List],Maxval):-
    find_biggest(List,Maxval,X).

find_biggest([],Currentlargest,Currentlargest).
find_biggest([A|L],Maxval,Currentlargest) :-
    A > Currentlargest,
    find_biggest(L,Maxval,A).
find_biggest([A|L],Maxval,Currentlargest) :-
    A =< Currentlargest,
    find_biggest(L,Maxval,Currentlargest).

?- find_largest([10,20,678,-4,-12,102,-5],M).
M = 678
?- find_largest([30,10],M).
M = 30
?- find_largest([234],M).
M = 234
```

- `front/2`: takes a list as its first argument. If the second argument is an unbound variable it is bound to a list which is the same as the first list with the last element removed

```Prolog
front([X],[]).
front([X|Y],[X|Z]) :- front(Y,Z).

?- front([alpha],L).
L = []
?- front([alpha,beta,gamma],LL).
LL = [alpha,beta]
?- front([[a,b],[c,d,e],[f,g,h]],L1).
L1 = [[a,b],[c,d,e]]
```

- implement `member`, `reverse` and `append`

```Prolog
mymember(X,[X|L]).
mymember(X,[_|L]) :- mymember(X,L).

myreverse(L1,L2) :- rev(L1,[],L2).
rev([],L,L).
rev([A|L],L1,L2) :- rev(L,[A|L1],L2).

myappend([],L,L).
myappend([A|L1],L2,[A|L3]) :- myappend(L1,L2,L3).

?- mymember(X,[a,b,c]).
X = a ;
X = b ;
X = c ;
false.
?- mymember(mypred(a,b,c),[q,r,s,mypred(a,b,c),w]).
true.
?- mymember(x,[]).
false.
?- myreverse([1,2,3,4],L).
L = [4,3,2,1]
?- myreverse([[dog,cat],[1,2],[bird,mouse],[3,4,5,6]],L).
L = [[3,4,5,6],[bird,mouse],[1,2],[dog,cat]]
?- myappend([1,2,3,4],[5,6,7,8,9],L).
L = [1,2,3,4,5,6,7,8,9]
?- myappend([],[1,2,3],L).
L = [1,2,3]
```

## 9.9 Using `findall/3` to Create a List

> [!note] findall/3

The predicate `findall` takes three arguments.

- The first is generally an unbound variable, but can be any term with at least one unbound variable as an argument.
- The second argument must be a goal, i.e. must be in a form that could appear on the right-hand side of a rule or be entered at the system prompt.
- The third argument should be an unbound variable.

Evaluating `findall` will cause this to be bound to a list of all the possible values of the term (first argument) that satisfy the goal (second argument).

```Prolog
person(john,smith,45,london).
person(mary,jones,28,edinburgh).
person(michael,wilson,62,bristol).
person(mark,smith,37,cardiff).
person(henry,roberts,23,london).

?- findall(S,person(_,S,_,_),L).
L = [smith,jones,wilson,smith,roberts]

?- findall([Forename,Surname],person(Forename,Surname,_,_),L).
L = [[john,smith],[mary,jones],[michael,wilson],[mark,smith],[henry,roberts]]

?- findall([londoner,A,B],person(A,B,_,london),L).
L = [[londoner,john,smith],[londoner,henry,roberts]]
```

```Prolog
age(john,45).
age(mary,28).
age(michael,62).
age(henry,23).
age(george,62).
age(bill,17).
age(martin,62).

oldest_list(L) :-
    findall(A,age(_,A),Agelist),
    find_largest(Agelist,Oldest),
    findall(Name,age(Name,Oldest),L).

find_under_30s(L) :- findall(Name,(age(Name,A),A<30),L).

?- oldest_list(L).
L = [michael,george,martin]

?- find_under_30s(L).
L = [mary,henry,bill]
```

# 10 String Processing

## 10.1 Converting Strings of Characters To and From Lists

> [!note] name/2

The predicate `name/2` takes two arguments.

- If the first is an atom and the second is an unbound variable, evaluating a `name` goal will cause the variable to be bound to a list of integers equivalent to the string of characters that forms the atom.

```Prolog
?- name('Prolog Example',L).
L = [80,114,111,108,111,103,32,69,120,97,109,112,108,101]

?-name(A,[80,114,111,108,111,103,32,69,120,97,109,112,108,101]).
A = 'Prolog Example'
```

## 10.2 Joining Two Strings

> [!example] "Joining Two Strings"

```Prolog
/* Join two strings String1 and String2 to form a
new string Newstring */
join2(String1,String2,Newstring) :-
    name(String1,L1),name(String2,L2),
    append(L1,L2,Newlist),
    name(Newstring,Newlist).

/* Join three strings using the join2 predicate */
join3(String1,String2,String3,Newstring) :-
    join2(String1,String2,S),
    join2(S,String3,Newstring).
```

```Prolog
?- join2('prolog','example',S).
S = 'prolog example'
?- join2('','Prolog',S).
S = 'Prolog'
?- join2('Prolog','',S).
S = 'Prolog'

?- join3('This is',' an',' example',Newstring).
Newstring = 'This is an example'
```

## 10.3 Trimming a String

> [!example] "Trimming a String"

```Prolog
trim([A|L],L1) :- A =< 32,trim(L,L1).
trim([A|L],[A|L]) :- A>32. /* 32 is the space character ASCII value */

?- trim([26,32,17,45,18,27,94,18,16,9],X).
X = [45,18,27,94,18,16,9]
```

```Prolog
trim2(L,L1) :-
    reverse(L,Lrev),trim(Lrev,L2),reverse(L2,L1).

?- trim2([45,18,27,94,18,16,9],X).
X = [45,18,27,94]
```

```Prolog
trim3(L,L1) :- trim(L,L2),trim2(L2,L1).

?- trim3([26,32,17,45,18,27,94,18,16,9],X).
X = [45,18,27,94]
```

```Prolog
trims(S,Snew):-name(S,L),trim3(L,L1),name(Snew,L1).

?- trims(' hello world ',X).
X = 'hello world'
```

## 10.4 Inputting a String of Characters


> [!example] "Inputting a String of Characters"

```Prolog
readline(S) :- readline1([],L),name(S,L),!.

readline1(Oldlist,L) :- get0(X),process(Oldlist,X,L).

process(Oldlist,10,Oldlist). /* the newline character ASCII value */
process(Oldlist,X,L) :-
    append(Oldlist,[X],L1),readline1(L1,L).

?- readline(S).
: abcdefg
S = abcdefg
?- readline(S).
: this is an example ,.C-*/#@ - Note no quotes needed and no final full stop
S = ' this is an example ,.C-*/#@ - Note no quotes needed and no final full stop'
```

```text title="file1.txt"
This is an example of
a text file with four lines -
each is terminated by an invisible character
with ASCII value 10
```

```Prolog
/* readline adapted for input from text files */
readlineF(File,S) :-
    see(File),readline1([],L),name(S,L),!,seen.

?- readlineF('file1.txt',S).
S = 'This is an example of '
```

## 10.5 Searching a String

> [!example] "Searching a String"

- separates a list L into those elements before and after the element 32

```Prolog
separate(L,Before,After) :-
    append(Before,[32|After],L),!.

?- separate([26,42,32,18,56,32,19,24],Before,After).
Before = [26,42] ,
After = [18,56,32,19,24]
?- separate([32,24,86],Before,After).
Before = [] ,
After = [24,86]
?- separate([24,86,32],Before,After).
Before = [24,86] ,
After = []
?- separate([24,98,45,72],Before,After).
false.
```

- `splitup`: split string by white space

```Prolog
separate(L,Before,After) :-
    append(Before,[32|After],L),!.

findnext(L) :-
    separate(L,Before,After),proc(Before,After).
findnext(L) :- write('Last item is '),
    name(S,L),write(S),nl.

proc(Before,After) :- write('Next item is '),
    name(S,Before),write(S),nl,findnext(After).

splitup(S) :- name(S,L),findnext(L).

?- splitup('The time has come the walrus said').
Next item is The
Next item is time
Next item is has
Next item is come
Next item is the
Next item is walrus
Last item is said
true.
```

- `checkprolog`: return `present` or `absent` depending on whether the input string include the word `Prolog`

```Prolog
/* Uses predicate readline as defined previously */
startList(L1,L2) :- append(L1,X,L2).

includedList(L1,[]) :- !,fail.
includedList(L1,L2) :- startList(L1,L2).
includedList(L1,[AjL2]) :- includedList(L1,L2).

checkit(L,Plist,present) :- includedList(Plist,L).
    checkit(_,_,absent).

checkprolog(X) :- readline(S),name(S,L),
    name('Prolog',Plist),checkit(L,Plist,X),!.

?- checkprolog(X).
: Logic Programming with Prolog
X = present
?- checkprolog(X).
: Mercury Venus Earth Mars Jupiter Saturn Uranus Neptune Pluto
X = absent
```

## 10.6 Dividing a String into Its Component Parts

> [!example] "Dividing a String"

- `splits/4`: divides a string into the substrings to the left and right of another string called a separator

```Prolog
splits(S,Separator,Separator,R):-
    name(Separator,L1),name(S,L3),
    append(L1,L2,L3),name(R,L2),!.
splits(S,Separator,L,Separator):-
    name(Separator,L2),name(S,L3),
    append(L1,L2,L3),name(L,L1),!.
splits(S,Separator,Left,Right):-
    name(S,L3),append(Lleft,Lrest,L3),
    name(Separator,L4),append(L4,Lright,Lrest),
    name(Left,Lleft),name(Right,Lright),!.
splits(S,_,S,''):-!.

?- splits('In the beginning was the word','the',Left,Right).
Left = 'In ' ,
Right = ' beginning was the word'
?- splits('my name is John Smith','is',Left,Right).
Left = 'my name ' ,
Right = ' John Smith'

?- splits('my name is John Smith','my name is ',Left,Right).
Left = 'my name is ' ,
Right = 'John Smith'
?- splits('my name is John Smith','John Smith',Left,Right).
Left = 'my name is ' ,
Right = 'John Smith'
?-splits('my name is my name is John Smith','is',Left,Right).
Left = 'my name ' ,
Right = ' my name is John Smith'
?- splits('my name is John Smith','Bill Smith',Left, Right).
Left = 'my name is John Smith' ,
Right = ''
```

- `remove_spaces`: remove any initial spaces from a string

```Prolog
remove_spaces(S,S1) :-
    splits(S,' ',Sleft,Sright),
    remove2(S,Sleft,Sright,S1),!.
remove2(S,' ',Sright,S1) :- remove_spaces(Sright,S1).
remove2(S,_,_,S).

?- remove_spaces('hello world',X).
X = 'hello world'
?- remove_spaces(' hello world',X).
X = 'hello world'
```

# 11 More Advanced Features

## 11.1 Introduction

More advanced features provided by Prolog:

- the use of operators to extend the language: new arithmetic operators, facilities for processing strings and sets
- facilities for processing terms: convert them to lists or evaluate them as goals.

## 11.2 Extending Prolog: Arithmetic

> [!example] "Add new operators"

```Prolog
?- op(700,xfx,iss).
?- op(150,xf,!). /* Factorial Operator */
?- op(120,yfx,**). /* Sum of Squares Operator */

factorial(1,1) :- !.
factorial(N,Y) :- N1 is N-1,factorial(N1,Y1),Y is N*Y1.

Y iss A**B :- A1 iss A, B1 iss B, Y is A1*A1+B1*B1,!.
Y iss sqrt(A) :- A1 iss A, Y is sqrt(A1),!.
Y iss N! :- N1 iss N,factorial(N1,Y),!.
Y iss A+B :- Y is A+B,!.
Y iss A-B :- Y is A-B,!.
Y iss A*B :- Y is A*B,!.
Y iss A/B :- Y is A/B,!.
Y iss A//B :- Y is A//B,!.
Y iss AˆB :- Y is AˆB,!.
Y iss +A :- Y is A,!.
Y iss -A :- Y is -A,!.
Y iss X :- Y is X,!.
```

```Prolog
?- Y iss 6+4*3-2.
Y = 16
?- X iss 3,Y iss X+5.6-3*10+100.5.
X = 3 ,
Y = 79.1
?-Y iss (8+4)/3-(6*7).
Y = -38
?- A=3,B=4,Y iss sqrt(A*A+B*B).
A = 3 ,
B = 4 ,
Y = 5.0
?- Y iss 6+sqrt(25).
Y = 11.0
?- Y iss 6+sqrt(10+15).
Y = 11.0

?- factorial(6,Y).
Y = 720

?-Y iss 6!.
Y = 720
?-Y iss (3+2)!.
YD 120
?- Y iss 5!+6!.
Y = 840
?- Y iss 4+2,Z iss Y!+3!-4!.
Y = 6 ,
Z = 702
?- Y iss (3!)!.
Y = 720
?- Y iss -(3!).
Y = -6

?- Y iss sqrt(3!).
Y = 2.449489742783178

?- Y iss 3**2.
Y = 13
?- Y iss (3**2)+2.
Y = 15
?- Y iss 6+3**4+8+1**2-10.
Y = 34
?- Y iss (3**1)**(2**1).
Y = 125
?- Y iss (3!)**(4!).
Y = 612.
```

Redefining Addition and Subtraction:

```Prolog
Y iss A+B :- A1 iss A,B1 iss B,Y is A1-B1,!.
Y iss A-B :- A1 iss A,B1 iss B,Y is A1+B1,!.

?- Y iss 6+4.
Y = 2
?- Y iss 6-4.
Y = 10
```

## 11.3 Extending Prolog: Operations on Strings

> [!note] atom/1

The built-in predicate `atom/1` tests whether or not a term is an atom.
The goal `atom(X)` succeeds if and only if `X` is an atom or a variable bound to an atom.

```Prolog
?- atom(a).
true
?- atom(X).
false
```

> [!example] "Define an operator `++` to join two strings"

```Prolog
?- op(700,xfx,iss).
?- op(150,xf,!). /* Factorial Operator */
?- op(120,yfx,**). /* Sum of Squares Operator */
?- op(200,yfx,++). /* String Join Operator */

factorial(1,1) :- !.
factorial(N,Y) :- N1 is N-1,factorial(N1,Y1),Y is N*Y1.

/* Join two strings String1 and String2 to form a new
string Newstring */
join2(String1,String2,Newstring) :-
  name(String1,L1),name(String2,L2),
  append(L1,L2,Newlist),
  name(Newstring,Newlist).

convert(X,X) :- atom(X).
convert(X,X1) :- X1 iss X.

S iss S1++S2 :- convert(S1,A),convert(S2,B),join2(A,B,S),!.
Y iss A**B :- A1 iss A, B1 iss B, Y is A1*A1+B1*B1,!.
Y iss sqrt(A) :- A1 iss A, Y is sqrt(A1),!.
Y iss N! :- N1 iss N,factorial(N1,Y),!.
Y iss A+B :- Y is A+B,!.
Y iss A-B :- Y is A-B,!.
Y iss A*B :- Y is A*B,!.
Y iss A/B :- Y is A/B,!.
Y iss A//B :- Y is A//B,!.
Y iss AˆB :- Y is AˆB,!.
Y iss +A :- Y is A,!.
Y iss -A :- Y is -A,!.
Y iss X :- Y is X,!.
```

```Prolog
?- S iss 'hello'++' world'.
S = 'hello world'
?- X='United States', Y='of America',Z iss X++' '++Y.
X = 'United States' ,
Y = 'of America' ,
Z = 'United States of America'
?- X='United States', Y='of America',Z iss 'This is the '++X++' '++Y.
X = 'United States' ,
Y = 'of America' ,
Z = 'This is the United States of America'
```

## 11.4 Extending Prolog: Sets

> [!example] "Set operations"

```Prolog
?- op(710,xfx,sis).
?- op(200,yfx,and).
?-op(200,yfx,or).

Y sis A and B :-
	A1 sis A,B1 sis B,
	findall(X,(member(X,A1),member(X,B1)),Y),!.

Y sis A or B:-
	A1 sis A,B1 sis B,
	findall(X,(member(X,A1);(member(X,B1),
	not(member(X,A1)))),Y),!.

Y sis A-B :-
	A1 sis A,B1 sis B,
	findall(X,(member(X,A1),not(member(X,B1))),Y),
	!.

A sis A :- !.
```

```Prolog
?- X=[a,b,c,d],Y=[e,b,f,c,g],Z=[a,e,c,g,h],A sis X and Y and Z.
X = [a,b,c,d] ,
Y = [e,b,f,c,g] ,
Z = [a,e,c,g,h] ,
A = [c]
?- X=[a,b,c,d],Y=[e,b,f,c,g],Z=[a,e,c,g,h],A sis X or Y or Z.
X = [a,b,c,d] ,
Y = [e,b,f,c,g] ,
Z = [a,e,c,g,h] ,
A = [a,b,c,d,e,f,g,h]
?- X=[a,b,c,d],Y=[e,b,f,c,g],Z=[a,e,c,g,h],A sis X-Y-Z.
X = [a,b,c,d] ,
Y = [e,b,f,c,g] ,
Z = [a,e,c,g,h] ,
A = [d]
```

## 11.5 Processing Terms

Prolog has several facilities for processing terms:

- decompose terms into their functor and arity
- extract a specified argument from a compound term
- convert terms to lists or vice versa
- evaluate a term as a goal

> [!note] =..

The built-in infix operator `=..` is known as 'univ'.

- Evaluating `X=..[member,A,L]` causes variable `X` to be bound to the term `member(A,L)`.
- Evalutting `X=..[colour,red]` causes `X` to be bound to the term `colour(read)`. `X` can then be used just like any other term.

```Prolog
?- X=..[colour,red],assertz(X).
X = colour(red)
?- colour(red).
true.
```

- If the first argument of 'univ` is a term and the second is an unbound variable, the latter is bound to a list that corresponds to the term, with the first element the functor and the remaing elements the arguments of the compound term in order.

```Prolog
?- data(6,green,mypred(26,blue))=..L.
L = [data, 6, green, mypred(26,blue)]
```

> [!note] call/1

The predicate `call/1` takes a single argument, which must be a call term, i.e. an atom or a compound term, or a variable bound to a call term.
The term is evaluated as if it were a goal.

```Prolog
?- call(write('hello world')).
hello world
true.
?- X=write('hello world'),call(X).
hello world
X = write('hello world')
```

`call/1` can be used to evaluate more than one goal if they are seperated by commas and enclosed in parentheses.

```Prolog
?- call((write('hello world'),nl,write('goodbye world'),nl)).
hello world
goodbye world
true.
?- X=(write('hello world'),nl),call(X).
hello world
X = (write('hello world'),nl)
```

used in conjuction with univ:

```Prolog
?- X=..[write,'hello world'],call(X).
hello world
X = write('hello world')

greet(Z) :- write('Hello '),write(Z),nl,
    write('How are you?'),nl.

?- X=..[greet,martin],call(X).
Hello martin
How are you?
X = greet(martin)
```

> [!note] functor/3

The built-in predicate `functor/3` takes three arguments.

- If the first argument is an atom or a compound term or a variable bound to one of those, and the other two arguments are unbound, the second argument will be bound to the functor of the first argument and the third will be bound to its arity. An atom is considered to have arity zero.

```Prolog
?- functor(write('hello world'),A,B).
A = write ,
B = 1
?- functor(city(london,england,europe),Funct,Ar).
Funct = city ,
Ar = 3
?- Z=person(a,b,c,d),functor(Z,F,A).
Z = person(a,b,c,d) ,
F = person ,
A = 4
?- functor(start,F,A).
F = start ,
A = 0
?- functor(a+b,F,A).
F = (+) ,
A = 2
```

- If the first argument is an unbound variable, the second is an atom, and the third is a positive integer, the variable is bound to a compound term with the given functor and arity, with all its arguments unbound variable. If the third argument is zero, the first argument is bound to an atom.

```Prolog
?- functor(T,person,4).
T = person(_42952,_42954,_42956,_42958)
?- functor(T,start,0).
T = start
```

> [!note] arg/3

The built-in predicate `arg/3` can be used to find a specified argument of a compound term.

- The first two arguments must be bound to a positive integer and a compound term, respectively.
- If the third argument is an unbound variable, it is bound to the value of the specified argument of the compound term.

```Prolog
?- arg(3,person(mary,jones,doctor,london),X).
X = doctor
?- N=2,T=person(mary,jones,doctor,london),arg(N,T,X).
N = 2 ,
T = person(mary,jones,doctor,london) ,
X = jones
```

> [!example] "Alternative implementation of `=/2`"

```Prolog
unify(CT1,CT2):-
    functor(CT1,Funct1,Arity1),
    functor(CT2,Funct2,Arity2),
    compare(CT1,CT2,Funct1,Arity1,Funct2,Arity2).

compare(CT1,CT2,F,0,F,0). /* Same atom*/
compare(CT1,CT2,F,0,F1,0) :- fail. /* Different atoms */
compare(CT1,CT2,F,A,F,A) :- unify2(CT1,CT2),!.
compare(CT1,CT2,_,_,_,_) :- fail.

unify2(CT1,CT2):-
    CT1=..[F|L1],CT2=..[F|L2],!,paircheck(L1,L2).

paircheck([],[]).
paircheck([A|L1],[A|L2]) :- paircheck(L1,L2).
```

```Prolog
?- unify(person(a,b,c,d),person(a,b,c,f)).
false.
?- unify(person(a,b,c,d),person(a,b,X,Y)).
X = c ,
Y = d
?- unify(pred(6,A,[X,Y,[a,b,c]],pred2(p,q)),pred(P1,Q1,L,Z)).
A = Q1 ,
P1 = 6 ,
L = [X,Y,[a,b,c]] ,
Z = pred2(p,q)
?- unify(person(a,b,c,d),person(a,b,X,X)).
false.
```


# 12 Using Grammar Rules to Analyse English Sentences

## 12.1 Introduction

- parser: `english_parser.pl`
- lexer: `english_lexer.pl`

## 12.2 Parsing English Sentences

> [!note] -->/2

The `-->/2` operator can be read is 'is a' or 'comprises' or 'is make up of'.

```Prolog
sentence-->noun,verb,noun.
sentence-->noun,verb.
```

Use `listing/1` to the corresponding regular Prolog clauses.

```Prolog
?-listing(sentence).
sentence(A, B) :-
    noun(A, C),
    verb(C, D),
    noun(D, B).
sentence(A, B) :-
    noun(A, C),
    verb(C, B).
```

> [!note] phrase/2

The special predicate `phrase/2` takes two arguments:

- the first is a syntactic term (the left hand side of the `-->/2` operator), 
- the second is a list of words.

Checks whether the list of words is valid in the syntactic term.

Use `{}` to include regular Prolog in a grammar rule clause.

> [!example] "Include regular Prolog in a grammar rule clause"

```Prolog
adjective-->[X],{ adjective_is(X) }.

adjective_is(large).
adjective_is(small).

adjective-->[brown].
adjective-->[orange].
adjective-->[green].
adjective-->[blue].
```

## 12.3 Converting Sentences to List Form

# 13 Prolog in Action

## 13.1 Implementing an Artificial Language

- `control_robot.pl`

> [!note] "Command for controlling the robot"

n,m: any numbers.

- `TURN n degrees anticlockwise`: Add n to current orientation
- `TURN n degrees clockwise`: Equivalent to `TURN -n degrees anticlockwise`
- `TURN RIGHT`: Equivalent to `TURN -90 degrees anticlockwise`
- `TURN LEFT`: Equivalent to `TURN 90 degrees anticlockwise`
- `TURN ROUND`: Equivalent to `TURN 180 degrees anticlockwise`
- `FORWARD n metres`: Go forward n metres using current orientation
- `BACK n metres`: Equivalent to `TURN ROUND` and then `FORWARD n metres`
- `GOTO n North m East`: Change position to n metres North and m metres East
- `FACE n degrees`: Change orientation to n degrees (anticlockwise from East)
- `REPORT`: State current position and orientation
- `STOP`: REPORT and then stop


## 13.2 Developing an Expert System Shell

- `quiz.pl`


# Appendix 1 Built-in Predicates

> [!note] !

Always succeeds. Used to control backtracking (see Chapter 7).

> [!note] append(Stream)

Similar to tell/1 but whereas for tell/1 any existing file with the same name is deleted, any existing file is not deleted and any output is placed after the end of the existing contents of the file (see Chapter 5). The predicate used for this may vary in different implementations of Prolog.

> [!note] append(First,Second,Whole)

Join or split lists (see Chapter 9).

> [!note] arg(N,Term,Arg)

N must be a positive integer and Term must be a compound term. Arg is unified with the Nth argument of Term.

> [!note] asserta(Clause)

Adds a clause to the definition of a predicate at the beginning of its sequence of existing clauses (if any).

> [!note] assertz(Clause)

Adds a clause to the definition of a predicate at the end of its sequence of existing clauses (if any).

> [!note] atom(Term)

Succeeds if and only if the given Term is a Prolog atom.

> [!note] atomic(Term)

Succeeds if and only if Term is an atom, a number, or a variable bound to either.

> [!note] call(Goal)

Calls the given Goal. Succeeds if Goal succeeds and fails if Goal fails.

> [!note] consult(Filename)

Loads the program contained in the named disk file.

> [!note] dynamic(predicate_specification)

Used to specify that a predicate is 'dynamic', i.e. may be modified (see Chapter 8).

> [!note] fail

Always fails. Used to force a program to backtrack.

> [!note] findall(Term,Goal,List)

Returns a list of all the instances of Term that satisfy goal Goal.

> [!note] functor(Term,Functor,Arity)

Succeeds if Term has the specified Functor and Arity.

> [!note] get(Char)

This reads the next 'printable' (i.e. non-white-space) character from the current input stream, and unifies Char with its integer character code.

> [!note] get0(Char)

This reads the next character from the current input stream, and unifies Char with its integer character code.

> [!note] halt

Terminates the current Prolog session and exits to the operating system.

> [!note] integer(Term)

Succeeds if and only if Term is an integer.

> [!note] length(List,Length)

Tests the length of a list (see Chapter 9).

> [!note] listing(Atom)

Lists all predicates with the given name, irrespective of their arity.

> [!note] member(Term,List)

Gets or checks a member of a list (see Chapter 9).

> [!note] name(Atom,List)

Converts between an atom and a list of characters (see Chapter 10).

> [!note] nl

Outputs a carriage return and line feed to the current output stream, to complete a line of output.

> [!note] op(Precedence,Type,Name)

Used to set, reset or clear the definition of an operator, using the given Precedence, Type and Name.

> [!note] phrase(Syntactic Term, List of Words)

Satisfied if the list of words is a valid example of the syntactic term (see Chapter 12).

> [!note] put(Integer)

Outputs the character corresponding to Integer to the current output stream.

> [!note] read(Var)

Reads a term from the current input stream and attempts to assign the value to Var, which should previously be unbound.

> [!note] repeat

Always succeeds when called, both when called and on backtracking. Used to provide a looping facility.

> [!note] retract(Clause)

Deletes the first matching clause from a predicate (see Chapter 8).

> [!note] retractall(Head)

Deletes all clauses whose heads match the given Head (see Chapter 8).

> [!note] reverse(List,Reverse)

Reverses the order of elements in a list (see Chapter 9).

> [!note] see(Stream)

Sets Stream to be the current input stream. Stream may be the name of a disk file or the atom user (referring to the console input device). If Stream refers to a disk file which is not open, it is automatically opened for reading. If the file is already open, input continues from the point immediately after the previously-read character.

> [!note] seeing(Stream)

Stream is bound to the name of the current input stream, which may be a disk file or the atom user (referring to the console input device).

> [!note] seen

Closes the file associated with the current input stream, and resets the current input stream to user.

> [!note] statistics

Displays statistics about the current session.

> [!note] tell(Stream)

Sets the current output stream, which may be a disk file or the atom user (referring to the console output device). Any existing disk file with the same name is deleted. If the file is already open, output continues from the point immediately after the previously written character.

> [!note] telling(Stream)

Gets the current output Stream, which may be a disk file or the atom user (referring to the console output device). Stream is bound to the name of the current output stream.

> [!note] told

Closes the file associated with the current output stream, and resets the current output stream to user.

> [!note] true

Always succeeds.

> [!note] write(Term)

Writes Term to the current output stream, in unquoted syntax.

> [!note] writeq(Term)

Writes Term to the current output stream, in quoted syntax.

# Appendix 2 Built-in Operators

> [!note] Goal1 , Goal2

Succeeds if and only if Goal1 and Goal2 are both true.

> [!note] Goal1 ; Goal2

Succeeds if either Goal1 or Goal2 is true (or both).

> [!note] Term1 = Term2

Succeeds if terms Term1 and Term2 unify (see Chapter 4).

> [!note] Term \= Term2

Succeeds if Term1 does not unify with Term2 (see Chapter 4).

> [!note] Term1 == Term2

Succeeds if Term1 is identical to Term2 (see Chapter 4).

> [!note] Term1 \== Term2

Succeeds if Term1 is not identical to Term2 (see Chapter 4).

> [!note] Exp1 =:= Exp2

Succeeds if the arithmetic expressions Exp1 and Exp2 evaluate to the same numerical value (see Chapter 4).

> [!note] Exp1 =\= Exp2

Succeeds if the arithmetic expressions Exp1 and Exp2 do not evaluate to the same numerical value (see Chapter 4).

> [!note] Term =.. List

Converts from a list to a term or vice versa (see Chapter 11).

> [!note] Exp1 < Exp2

Succeeds if the value of arithmetic expression Exp1 is less than the value of arithmetic expression Exp2.

> [!note] Exp1 =< Exp2

Succeeds if the value of arithmetic expression Exp1 is less than or equal to the value of arithmetic expression Exp2.

> [!note] Exp1 > Exp2

Succeeds if the value of arithmetic expression Exp1 is greater than the value of arithmetic expression Exp2.

> [!note] Exp1 >= Exp2

Succeeds if the value of arithmetic expression Exp1 is greater than or equal to the value of arithmetic expression Exp2.

> [!note] head --> body

Used in grammar rules (see Chapter 12).

> [!note] Result is Expression

Expression must be a valid arithmetic expression which is evaluated to give a number. If Result is an unbound variable (the usual case) the variable is bound to the value of the expression. If Result is a bound variable with a numerical value or a number, the goal succeeds if the values of both sides of the is operator are the same and fails otherwise.

> [!note] not Goal

Succeeds if Goal fails, fails if Goal succeeds.

Note: in some versions of Prolog not/1 is defined as a predicate with one argument but not as an operator. In such cases it can be made into an operator as shown in Section 4.4.