----------------------------- MODULE EuclidAlg -----------------------------
EXTENDS Naturals, TLC

CONSTANT N

(*--algorithm EuclidAlg
variables u = 24,
          v \in 1..N,
          v_ini = v;
          

begin 
    while u /= 0 do
        if u < v then u := v || v := u; \* swap
        end if;
        u := u - v;
    end while;
    print <<24, v_ini, "have gcd", v>>;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "d7618650" /\ chksum(tla) = "b567e1c7")
VARIABLES u, v, v_ini, pc

vars == << u, v, v_ini, pc >>

Init == (* Global variables *)
        /\ u = 24
        /\ v \in 1..N
        /\ v_ini = v
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF u /= 0
               THEN /\ IF u < v
                          THEN /\ /\ u' = v
                                  /\ v' = u
                          ELSE /\ TRUE
                               /\ UNCHANGED << u, v >>
                    /\ pc' = "Lbl_2"
               ELSE /\ PrintT(<<24, v_ini, "have gcd", v>>)
                    /\ pc' = "Done"
                    /\ UNCHANGED << u, v >>
         /\ v_ini' = v_ini

Lbl_2 == /\ pc = "Lbl_2"
         /\ u' = u - v
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << v, v_ini >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Wed May 15 18:35:47 CST 2024 by zhouj
\* Created Wed May 15 18:18:53 CST 2024 by zhouj
