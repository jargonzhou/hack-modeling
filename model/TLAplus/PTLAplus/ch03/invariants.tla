---- MODULE invariants ----
EXTENDS Integers, Sequences

AllLessThan(set, max) == \A num \in set: num < max
\* AllLessThan({1,3}, 4) \* TRUE
\* AllLessThan({1, 3}, 2) \* FALSE
\* AllLessThan({1, 3}, "FOO") \* Error

\* logical operators: \A, \E, =>, <=>

SeqOverlapsSet(seq, set) == \E x \in 1..Len(seq): seq[x] \in set
\* SeqOverlapsSet(<<1, 3>>, {2, 3, 4}) \* TRUE

IsCommutativeOver(Op(_,_), S) == 
    \A x,y \in S: Op(x,y) = Op(y,x)
IsCommutativeOver2(Op(_,_), S) == 
    \A x \in S, y \in S: Op(x,y) = Op(y,x)
IsCommutativeOver3(Op(_,_), S) == 
    \A <<x,y>> \in S \X S : Op(x,y) = Op(y,x)
\* IsCommutativeOver(LAMBDA x, y: x + y, 1..10) \* TRUE
\* IsCommutativeOver(LAMBDA x, y: x - y, 1..10) \* FALSE

Xor(A,B) == (~A /\ B) \/ (A /\ ~B)
OtherXor(A,B) == ~A <=> B
INV == \A A \in BOOLEAN, B \in BOOLEAN: Xor(A,B) = OtherXor(A,B) \* TRUE

\* expressions

Max(x,y) == IF x > y THEN x ELSE y
\* <<Max(2,3), Max(3,2)>> \* <<3, 3>>
VAR(x) == CASE x = 1 -> TRUE
         [] x = 2 -> TRUE
         [] x = 3 -> 7
         [] OTHER -> FALSE
\* VAR(1) \* TRUE
\* VAR(2) \* TRUE
\* VAR(3) \* 7
\* VAR(4) \* FALSE

IndexOf(seq, elem) ==
    CHOOSE i \in 1..Len(seq): seq[i] = elem
\* IndexOf(<<8, 3, 1>>, 3) \* 2
\* IndexOf(<<8, 3, 1>>, 4) \* Error
Max2(set) == CHOOSE x \in set: \A y \in set: x >= y
\* Max2(1..10) \* 10
SOLUTION == CHOOSE <<x,y>> \in (-10..10) \X (-10..10):
    /\ 2 * x + y = -2
    /\ 3 * x - 2 * y = 11
\* <<1, -4>>
====