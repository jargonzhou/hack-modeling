# TLA+ Version 2:  A Preliminary Guide


# 1 Introduction
# 2 Recursive Operator Definitions
# 3 Lambda Expressions

```TLA+
F(Op(_,_)) == Op(1,2)
Id(a,b) == a + 2 * b
F(Id)

F(LAMBDA a,b : a + 2 * b)

INSTANCE M WITH Op <- Id
INSTANCE M WITH Op <- LAMBDA a,b : a + 2 * b
```
# 4 Theorems and Assumptions

```TLA+
THEOREM Fermat == ~(\E n \in Nat \ (1..2): ...)
\* synonyms
LEMMA
PROPOSITION

ASSUME
\* synonyms
ASSUMPTION
AXIOM \* TLC does not check these assumptions
```


```TLA+
THEOREM DeductionRule == ASSUME NEW P, NEW Q,
								ASSUME P
								PROVE Q
						PROVE P => Q

THEOREM ASSUME NEW P(_), NEW S,
				ASSUME NEW x \in S
				PROVE P(x)
		PROVE \A x \in S : P(x)

\* primed constant equals itself
THEOREM Constancy == ASSUME CONSTANT C
					 PROVE C' = C

\* a temporal-logic rule
THEOREM ASSUME TEMPORAL F, TEMPORAL G
		PROVE [](F /\ G) <=> []F /\ []G

\* variable v.s. state ???
THEOREM ASSUME VARIABLE x, VARIABLE y
		PROVE ENABLED x' /= y'
```
# 5 Instantiation 

Leibniz operator
```TLA+
e = f => F(e) = F(f)
F(e1, ..., ek)
```

constant module???
Specifying Systems P.330
constant operator???
```TLA+
\* Specifying Systems P.46
CONSTANT Send(_,_,_,_)
```
# 6 Naming Subexpressions
- lables and labeled subexpression names
```TLA+
label :: expression

a + lab :: b * c \* a + (lab :: (b * c))
\* illegal: a * (b + c) /= a * b + c
a * lab :: b + c

\* within the scope of bound identifier
F(a) == \A b : l1(b) :: (a > 0) =>
                              /\ ...
                              /\ l2 :: \E c : /\ ...
				                              /\ \E d : l3(c,d) :: a - b > c - d
F(A)!l1(B)!l2!l3(C,D) \* A - B > C - D

Ins(x) == INSTANCE M WITH ... \* v is the name of any subexpression of a definition in M
Ins(exp)!v
```
- positional subexpression names
```TLA+
F(a) == /\ ...
		/\ ...
		/\ Len(x[a]) > 0
		/\ ...
F(A)!3       \* Len(x[A]) > 0
F(A)!3!1     \* Len(x[A])
F(A)!3!1!1   \* x[A]
F(A)!3!1!1!1 \* x
F(A)!3!1!1!2 \* A
	F(A)!3!<<!<<!>>

!<< \* synonymous with !1
!>> \* synonymous with !2

[f EXCEPT ![a] = g, ![b].c = h]
	!1 \* f
	!2 \* g
	!3 \* h
r.fld
[fld1 |-> val1, ..., fldn |-> valn]
IF p THEN e ELSE f
CASE p1 -> e1 [] ... [] pn -> en
WF_e(A)
SF_e(A)
[A]_e
<<A>>_e
LET ... IN e

R == \E x \in S, y \in T : x + y > 2
\[x,y \in S, z \in T |-> x + y + z] \* comment with markdown formating
```
- subexpressions of `LET` definitions
```TLA+
F(A) == /\ ...
		/\ LET G(b) == a + b
		   IN ...
F(A)!2!G(B)    \* G(B)
F(A)!2!G(B)!>> \* B

λ!Op(e1,...,en)
λ!:!Op(e1,...,en)
```
- subexpressions of an `ASSUME/PROVE`
- using subexpression names as operators

# 7 The Proof Syntax
**TLAPS**: the TLA+ proof checker

- the structure of a proof
- `USE`, `HIDE`, `BY`
	- `OBVIOUS`, `OMITTED`
- the current state
- steps that take proof
	- formulas, `ASSUME/PROVE`
	- `CASE`
	- `@` steps
	- `SUFFICES`
	- `PICK`
	- `QED`
- steps that do not take proof
	- definitions
	- `INSTANCE`
	- `USE`, `HIDE`
	- `HAVE`
	- `TAKE`
	- `WITNESS`
- referring to steps and their parts
	- naming subexpressions
	- naming facts
	- naming definitions
- referring to instantiated theorems
- temporal proofs
# 8 The Semantics of Proofs
- the meaning of boolean operators
- the meaning of `ASSUME/PROVE`
- temporal proofs
