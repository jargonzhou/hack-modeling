---- MODULE operators----
EXTENDS TLC, Integers, Sequences

\* high order operators
Add(a, b) == a + b
Apply(op(_,_), x, y) == op(x,y)

\* Apply(Add, 1, 2) \* 3
\* Apply(LAMBDA x,y: x + y, 1, 2) \* 3

\* user defined operators
set ++ elem == set \union {elem}
set -- elem == set \ {elem}
\* {1,2} ++ 3 \* {1,2,3}
\* {1,2} -- 2 \* {1}
====