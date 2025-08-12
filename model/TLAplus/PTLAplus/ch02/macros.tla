---- MODULE macros ----
EXTENDS TLC

(**--algorithm macros
variables x = FALSE;

macro set_x() begin
    x := TRUE;
end macro;

begin
    set_x();
    assert x;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "ac6aabc" /\ chksum(tla) = "819334de")
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x = FALSE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ x' = TRUE
         /\ Assert(x', "Failure of assertion at line 13, column 5.")
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
