---- MODULE knapsack ----
EXTENDS TLC, Integers, Sequences, Naturals
\* constants
CONSTANTS Capacity, Items, SizeRange, ValueRange
ASSUME Capacity \in Nat \ {0}
ASSUME SizeRange \subseteq Nat
ASSUME  \A v \in ValueRange: v >= 0
\* Capacity == 7
\* Items == {"a", "b", "c"}
ItemParams == [size: SizeRange, value: ValueRange]
ItemSets == [Items -> ItemParams]

PT == INSTANCE PT

HardcodedItemSet == [
    a |-> [size |-> 1, value |-> 1],
    b |-> [size |-> 2, value |-> 3],
    c |-> [size |-> 3, value |-> 1]
]

KnapsackSize(sack, itemset) ==
    LET size_for(item) == itemset[item].size * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: size_for(item) + acc, Items, 0)

ValidKnapsacks(itemset) ==
    {sack \in [Items -> 0..4]: KnapsackSize(sack, itemset) <= Capacity}

KnapsackValue(sack, itemset) ==
    LET value_for(item) == itemset[item].value * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: value_for(item) + acc, Items, 0)

BestKnapsack(itemset) ==
    LET
        value(sack) == KnapsackValue(sack, itemset)
        all == ValidKnapsacks(itemset)
        best == CHOOSE best \in all:
            \A worse \in all \ {best}:
                value(best) >= value(worse)
    IN
        {k \in all: value(best) = value(k)}

(**--algorithm knapsack
variables itemset \in ItemSets;
begin
    assert BestKnapsack(itemset) \subseteq ValidKnapsacks(itemset)
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "5941852f" /\ chksum(tla) = "fe1f4581")
VARIABLES itemset, pc

vars == << itemset, pc >>

Init == (* Global variables *)
        /\ itemset \in ItemSets
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(BestKnapsack(itemset) \subseteq ValidKnapsacks(itemset), 
                   "Failure of assertion at line 45, column 5.")
         /\ pc' = "Done"
         /\ UNCHANGED itemset

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
