---- MODULE functions ----
EXTENDS TLC, Integers, Sequences

VAR1 == [x \in 1..2 |-> x*2] \* <<2, 4>>
VAR2 == Head([x \in 1..2 |-> x*2]) \* 2

MapToSomeNumber(set, num) == [x \in set |-> num]
\* MapToSomeNumber(1..2,3) \* <<3, 3>>

SumUpTo(n) ==
    LET F[m \in 0..n] ==
        IF m = 0 THEN 0
        ELSE m + F[m-1]
    IN F[n]
\* SumUpTo(10) \* 55

\* DOMAIN
F[x \in BOOLEAN] == x
G == <<6,0,9>>
H == [F |-> DOMAIN F, G |-> DOMAIN G] \* [F |-> {FALSE, TRUE}, G |-> 1..3]
\* DOMAIN H \* {"F", "G"}

\* @@
ff[x \in 1..2] == "a"
gg[x \in 2..3] == "b"
\* ff @@ gg \* <<"a", "a", "b">>
\* gg @@ ff \* <<"a", "b", "b">>

\* a :> b means [x \in {a} |-> b]
\* (2 :> 3)[2] \* 3
\* ("a" :> "b").a \* "b"

\* set of functions: [set1 -> set2]
\* [s \in {"a","b"} |-> {1,2}] \* [a |-> {1, 2}, b |-> {1, 2}]
\* [{"a", "b"} -> {1, 2}] \* {[a |-> 1, b |-> 1], [a |-> 1, b |-> 2], [a |-> 2, b |-> 1], [a |-> 2, b |-> 2]}

SeqOf(set, count) == [1..count -> set]
\* SeqOf({"a","b","c"},2) \* {<<"a", "a">>, <<"a", "b">>, <<"a", "c">>, <<"b", "a">>, <<"b", "b">>, <<"b", "c">>, <<"c", "a">>, <<"c", "b">>, <<"c", "c">>}

Flags == {"f1", "f2"}
(**--algorithm flags
variables
    \* flags = [f \in Flags |-> FALSE];
    \* flags \in [Flags -> BOOLEAN]
    \* at least one flag is true
    flags \in {config \in [Flags -> BOOLEAN]: \E f \in Flags: config[f]}

begin
    with f \in Flags do
        flags[f] := TRUE;
    end with;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "f1035d74" /\ chksum(tla) = "6ac47696")
VARIABLES flags, pc

vars == << flags, pc >>

Init == (* Global variables *)
        /\ flags \in {config \in [Flags -> BOOLEAN]: \E f \in Flags: config[f]}
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ \E f \in Flags:
              flags' = [flags EXCEPT ![f] = TRUE]
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
