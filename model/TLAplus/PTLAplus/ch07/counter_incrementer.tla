Eventually Always (<>[]) in multiprocess algorithm.

---- MODULE counter_incrementer ----
EXTENDS TLC, Integers, Sequences

(**--algorithm counter_incrementer
variables 
    counter = 0,
    goal = 3;

define
    Success == <>[](counter = goal)
end define;

fair process incrementer \in 1..3
variable local = 0
begin
    \* Get:
    \*     local := counter;
    \* Increment:
    \*     counter := local + 1;
    GetAndIncrement:
        local := counter;
        counter := local + 1;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "faa4272e" /\ chksum(tla) = "4300bc5e")
VARIABLES counter, goal, pc

(* define statement *)
Success == <>[](counter = goal)

VARIABLE local

vars == << counter, goal, pc, local >>

ProcSet == (1..3)

Init == (* Global variables *)
        /\ counter = 0
        /\ goal = 3
        (* Process incrementer *)
        /\ local = [self \in 1..3 |-> 0]
        /\ pc = [self \in ProcSet |-> "GetAndIncrement"]

GetAndIncrement(self) == /\ pc[self] = "GetAndIncrement"
                         /\ local' = [local EXCEPT ![self] = counter]
                         /\ counter' = local'[self] + 1
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ goal' = goal

incrementer(self) == GetAndIncrement(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..3: incrementer(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..3 : WF_vars(incrementer(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
