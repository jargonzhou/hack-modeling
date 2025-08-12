---- MODULE LLTest ----
EXTENDS TLC, FiniteSets

CONSTANTS Nodes, NULL

LL == INSTANCE LL WITH NULL <- NULL
AllLL == LL!LL(Nodes)

(**--algorithm binary_search
variables
    cyclic_not_ring = CHOOSE ll \in LL!LL({"a", "b"}): LL!Cyclic(ll) /\ ~LL!Ring(ll)

define
    CycleImpliesTowParents(ll) ==
        LL!Cyclic(ll) <=>
            \/ LL!Ring(ll)
            \/ \E n \in DOMAIN ll: Cardinality({p \in DOMAIN ll: ll[p] = n}) = 2
        
    Valid ==
        /\ \A ll \in AllLL:
            /\ Assert(CycleImpliesTowParents(ll), <<"Counter example: ", ll>>)
end define;

begin
    assert cyclic_not_ring \in {[a |-> "a", b |-> "a"], [a |-> "b", b |-> "b"]}
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "a1a932ea" /\ chksum(tla) = "d6b7878f")
VARIABLES cyclic_not_ring, pc

(* define statement *)
CycleImpliesTowParents(ll) ==
    LL!Cyclic(ll) <=>
        \/ LL!Ring(ll)
        \/ \E n \in DOMAIN ll: Cardinality({p \in DOMAIN ll: ll[p] = n}) = 2

Valid ==
    /\ \A ll \in AllLL:
        /\ Assert(CycleImpliesTowParents(ll), <<"Counter example: ", ll>>)


vars == << cyclic_not_ring, pc >>

Init == (* Global variables *)
        /\ cyclic_not_ring = (CHOOSE ll \in LL!LL({"a", "b"}): LL!Cyclic(ll) /\ ~LL!Ring(ll))
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(cyclic_not_ring \in {[a |-> "a", b |-> "a"], [a |-> "b", b |-> "b"]}, 
                   "Failure of assertion at line 25, column 5.")
         /\ pc' = "Done"
         /\ UNCHANGED cyclic_not_ring

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
