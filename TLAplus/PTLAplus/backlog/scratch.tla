------------------------------ MODULE scratch ------------------------------
EXTENDS Integers, TLC, FiniteSets, Sequences

Eval == 0
Range == 1..3

CardinalityOfSet == Cardinality({"a", "b"})

AllLessThan(set, max) == \A num \in set: num < max

SeqOverlapsSet(seq, set) == \E x \in 1..Len(seq): seq[x] \in set

SetOverlapsSet(set1, set2) == \E x \in set1: x \in set2

IsCommutativeOver(Op(_, _), S) ==
    \A x, y \in S: Op(x, y) = Op(y, x)
\* IsCommutativeOver(LAMBDA x, y: x - y, 1..10)
\* FALSE

Xor(A, B) == (~A /\ B) \/ (A /\ ~B)
OtherXor(A, B) == ~A <=> B
    
\* \A A \in BOOLEAN, B \in BOOLEAN: Xor(A, B) = OtherXor(A, B)
\* TRUE

SeqOf(set, count) == [1..count -> set]

\* SeqOf({"a", "b", "c"}, 2)
\*{ <<"a", "a">>,
\*     <<"a", "b">>,
\*     <<"a", "c">>,
\*     <<"b", "a">>,
\*     <<"b", "b">>,
\*     <<"b", "c">>,
\*     <<"c", "a">>,
\*     <<"c", "b">>,
\*     <<"c", "c">> }


(*--algorithm scratch

\*define
\*    skip;
\*end define;

begin
    skip;
end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "2614515e" /\ chksum(tla) = "af3d9146")
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Fri Aug 19 15:05:08 CST 2022 by zhoujiagen
\* Created Tue Aug 16 14:45:40 CST 2022 by zhoujiagen
