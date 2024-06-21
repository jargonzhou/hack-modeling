---- MODULE in ----
EXTENDS TLC, Integers, Sequences

(**--algorithm in
variables x \in 1..3; \* multiple starting states
begin
    assert x <= 3;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "4e01d062" /\ chksum(tla) = "21dd3d77")
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x \in 1..3
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(x <= 3, "Failure of assertion at line 7, column 5.")
         /\ pc' = "Done"
         /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
