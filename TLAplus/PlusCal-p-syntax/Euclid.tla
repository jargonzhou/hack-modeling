------------------------------- MODULE Euclid -------------------------------
(* PlusCal options (-termination) *)

EXTENDS Naturals, TLC

CONSTANT N

(*--algorithm EuclidAlg
variables u = 24,
          v \in 1..N,
          v_ini = v;
      
define
    gcd(x,y) == CHOOSE i \in 1..x :
                    /\ x % i = 0
                    /\ y % i = 0
                    /\ \A j \in 1..x : /\ x % j = 0
                                       /\ y % j = 0
                                       => i >= j
end define;
    
begin 
    while u /= 0 do
        if u < v then u := v || v := u; \* swap
        end if;
        u := u - v;
    end while;
    assert v = gcd(24, v_ini);
    print <<24, v_ini, "have gcd", v>>;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "7906d86c" /\ chksum(tla) = "9997bc3b")
VARIABLES u, v, v_ini, pc

(* define statement *)
gcd(x,y) == CHOOSE i \in 1..x :
                /\ x % i = 0
                /\ y % i = 0
                /\ \A j \in 1..x : /\ x % j = 0
                                   /\ y % j = 0
                                   => i >= j


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
               ELSE /\ Assert(v = gcd(24, v_ini), 
                              "Failure of assertion at line 28, column 5.")
                    /\ PrintT(<<24, v_ini, "have gcd", v>>)
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

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Mon May 20 11:16:41 CST 2024 by zhouj
\* Created Mon May 20 10:58:08 CST 2024 by zhouj
