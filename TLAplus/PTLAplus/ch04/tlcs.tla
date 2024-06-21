---- MODULE tlcs ----
EXTENDS TLC, Integers, Sequences
\* CONSTANTS N

VAR1 == Print(<<"2 + 3 =", 5>>, <<1>>) \o <<2>> \* <<1, 2>>
VAR2 == PrintT(<<"2 + 3 =", 5>>) \* TRUE

VAR3 == Assert(3 < 5, "3 is more than 5") \* TRUE

\* Error evaluating expression:
\* The first argument of Assert evaluated to FALSE; the second argument was:
\* "3 is more than 5"
VAR4 == LET x == 3
            y == 5
        IN Assert(x > y, ToString(x) \o " is more than " \o ToString(y))

VAR5 == Permutations({1,2,3})
\* {<<1, 2, 3>>, <<1, 3, 2>>, <<2, 1, 3>>, <<2, 3, 1>>, <<3, 1, 2>>, <<3, 2, 1>>}
VAR6 == SortSeq(<<1,2,3>>, LAMBDA x,y: x > y) \* <<3, 2, 1>>

\* CHOOSE seq \in Permutations({1,2,3}): TRUE \* <<1, 2, 3>>
====

