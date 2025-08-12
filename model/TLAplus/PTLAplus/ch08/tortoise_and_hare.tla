The Tortoise and the Hare algorithm: detecint cycles in linked list.

---- MODULE tortoise_and_hare ----
EXTENDS TLC
CONSTANTS Nodes, NULL
INSTANCE LL

(**--fair algorithm tortoise_and_hare
variables 
    ll \in LL(Nodes),
    tortoise = First(ll),
    hare = tortoise;

macro advance(pointer) begin
    pointer := ll[pointer];
    if pointer = NULL then
        assert ~Cyclic(ll);
        goto Done;
    end if;
end macro;

begin
    while TRUE do
        advance(tortoise);
        advance(hare);
        advance(hare);
        if tortoise = hare then
            assert Cyclic(ll);
            goto Done;
        end if;
    end while;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "3c42eca2")
VARIABLES ll, tortoise, hare, pc

vars == << ll, tortoise, hare, pc >>

Init == (* Global variables *)
        /\ ll \in LL(Nodes)
        /\ tortoise = First(ll)
        /\ hare = tortoise
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ tortoise' = ll[tortoise]
         /\ IF tortoise' = NULL
               THEN /\ Assert(~Cyclic(ll), 
                              "Failure of assertion at line 17, column 9 of macro called at line 24, column 9.")
                    /\ pc' = "Done"
               ELSE /\ pc' = "Lbl_2"
         /\ UNCHANGED << ll, hare >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ hare' = ll[hare]
         /\ IF hare' = NULL
               THEN /\ Assert(~Cyclic(ll), 
                              "Failure of assertion at line 17, column 9 of macro called at line 25, column 9.")
                    /\ pc' = "Done"
               ELSE /\ pc' = "Lbl_3"
         /\ UNCHANGED << ll, tortoise >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ hare' = ll[hare]
         /\ IF hare' = NULL
               THEN /\ Assert(~Cyclic(ll), 
                              "Failure of assertion at line 17, column 9 of macro called at line 26, column 9.")
                    /\ pc' = "Done"
               ELSE /\ pc' = "Lbl_4"
         /\ UNCHANGED << ll, tortoise >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ IF tortoise = hare
               THEN /\ Assert(Cyclic(ll), 
                              "Failure of assertion at line 28, column 13.")
                    /\ pc' = "Done"
               ELSE /\ pc' = "Lbl_1"
         /\ UNCHANGED << ll, tortoise, hare >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
