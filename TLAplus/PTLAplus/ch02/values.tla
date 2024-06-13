---- MODULE values ----
EXTENDS Integers, TLC, FiniteSets, Sequences

(* string, integer, boolean *)
String == "PlusCal"
Integer == 0
Boolean == TRUE

(* Operators *)
Equals == 1 = 2             \* FALSE
NotEquals == 1 /= 2         \* TRUE
NotEquals2 == 1 # 2         \* TRUE
And == TRUE /\ FALSE        \* FALSE
Or == TRUE \/ FALSE         \* TRUE
\* Assignment == x := 1
Not == ~TRUE                \* FALSE

\* EXTENDS Integers
\* arithmetic
ADD == 1 + 2                \* 3
SUB == 1 - 2                \* -1
MUL == 5 * 3                \* 15
DIV == 5 \div 3             \* 1
MOD == 5 % 3                \* 2
\* range
RANGE == 1..3               \* 1..3


(* sets *)
IsElementOfSet == 1 \in 1..2                        \* TRUE
IsNotElementOfSet == 1 \notin 1..2                  \* FALSE
IsNotElementOfSet2 == ~(1 \in 1..2)                 \* FALSE
IsSubsetOfSet == {1, 2} \subseteq {1, 2, 3}         \* TRUE
SetUnion == 1..2 \union 2..3                        \* {1, 2, 3}
SetIntersection == 1..2 \intersect 2..3             \* {2}
SetDifference == 1..2 \ 2..3                        \* {1}
CardinalityOfSet == Cardinality({"a", "b"})         \* 2

\* set transformations
FilterSet == {x \in 1..2: x < 2}                    \* {1}
MapSet == {x * 2: x \in 1..2}                       \* {2, 4}

(* tuples/sequence *)
HeadOfSequence == Head(<<1, 2>>)                    \* 1
TailOfSequence == Tail(<<1, 2, 3>>)                 \* <<2, 3>>
AppendSequence == Append(<<1, 2>>, 3)               \* <<1, 2, 3>>
CombineSequence == <<1>> \o <<2, 3>>                \* <<1, 2, 3>>
LengthOfSequence == Len(<<1, 2, 3, 4>>)             \* 4

(* structures *)
Structure == [a |-> 1, b |-> <<1, {}>>]             \* [a |-> 1, b |-> <<1, {}>>]
StructureKeyValue == [a |-> 1, b |-> <<1, {}>>].b   \* <<1, {}>>

(*--algorithm values
    variables
        x = <<1, [a |-> {}]>>;

begin
    x[2].a := x[2].a \union {2}
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "5c7b854e" /\ chksum(tla) = "1f844143")
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x = <<1, [a |-> {}]>>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ x' = [x EXCEPT ![2].a = x[2].a \union {2}]
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
