---- MODULE pointtest ----
EXTENDS TLC
INSTANCE Point WITH X <- 1, Y <- 2

P1 == INSTANCE Point WITH X <- 1, Y <- 2
P2 == INSTANCE Point WITH X <- 2, Y <- 1

PV1(Y) == INSTANCE Point WITH X <- 1
PV2(X) == INSTANCE Point WITH Y <- 1
PV3(X,Y) == INSTANCE Point

(**--algorithm test
begin
    assert Point = <<1,2>>;
    assert Add(3,4) = <<4,6>>;

    assert P1!Point = <<1,2>>;
    assert P2!Point = <<2,1>>;

    assert PV1(3)!Point = <<1,3>>;
    assert PV2(3)!Add(1,1) = <<4,2>>;
    assert PV3(1,2)!Add(2,3) = <<3,5>>;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "4cbe3ec6" /\ chksum(tla) = "1e57ccdd")
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(Point = <<1,2>>, 
                   "Failure of assertion at line 14, column 5.")
         /\ Assert(Add(3,4) = <<4,6>>, 
                   "Failure of assertion at line 15, column 5.")
         /\ Assert(P1!Point = <<1,2>>, 
                   "Failure of assertion at line 17, column 5.")
         /\ Assert(P2!Point = <<2,1>>, 
                   "Failure of assertion at line 18, column 5.")
         /\ Assert(PV1(3)!Point = <<1,3>>, 
                   "Failure of assertion at line 20, column 5.")
         /\ Assert(PV2(3)!Add(1,1) = <<4,2>>, 
                   "Failure of assertion at line 21, column 5.")
         /\ Assert(PV3(1,2)!Add(2,3) = <<3,5>>, 
                   "Failure of assertion at line 22, column 5.")
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
