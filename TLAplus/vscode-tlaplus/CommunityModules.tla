---- MODULE  CommunityModules----
\* EXTENDS TLC, Integers, Sequences

CSV == INSTANCE CSV

TEST == CSV!CSVWrite("%1$s#%2$s#%3$s", <<"abc", 42, {"x", "y"} >>, "out.csv")

\* BEGIN TRANSLATION (chksum(pcal) = "b5cc3d41" /\ chksum(tla) = "3e8b2e09")
VARIABLES a, pc

vars == << a, pc >>

Init == (* Global variables *)
        /\ a = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ a' = CSV!CSVWrite("%1$s#%2$s#%3$s", <<"abc", 42, {"x", "y"} >>, "out.csv")
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
