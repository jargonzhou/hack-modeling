---- MODULE knapsack ----
EXTENDS TLC, Integers, Sequences
PT == INSTANCE PT

Capacity == 7
Items == {"a", "b", "c"}
ItemParams == [size: 2..4, value: 0..5]
ItemSets == [Items -> ItemParams]

HardcodedItemSet == [
    a |-> [size |-> 1, value |-> 1],
    b |-> [size |-> 2, value |-> 3],
    c |-> [size |-> 3, value |-> 1]
]

\* sack: ex [a |-> n1, b |-> n2, c |-> n3]
KnapsackSize(sack, itemset) ==
    LET size_for(item) == itemset[item].size * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: size_for(item) + acc, Items, 0)

ValidKnapsacks(itemset) ==
    {sack \in [Items -> 0..4]: KnapsackSize(sack, itemset) <= Capacity}

KnapsackValue(sack, itemset) ==
    LET value_for(item) == itemset[item].value * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: value_for(item) + acc, Items, 0)

BestKnapsack(itemset) ==
    \* LET all == ValidKnapsacks(itemset)
    \* IN CHOOSE best \in all:
    \*     \A worse \in all \ {best}:
    \*     KnapsackValue(best, itemset) > KnapsackValue(worse, itemset)
    LET
        value(sack) == KnapsackValue(sack, itemset)
        all == ValidKnapsacks(itemset)
        best == CHOOSE best \in all:
            \A worse \in all \ {best}:
                value(best) >= value(worse)
    IN
        {k \in all: value(best) = value(k)}

\* {BestKnapsack(is) : is \in ItemSets}
\* {ValidKnapsacks(is) : is \in ItemSets}

(**--algorithm knapsack
variables itemset \in ItemSets;
begin
    \* assert BestKnapsack(HardcodedItemSet) = [a |-> 1, b |-> 3, c |-> 0]
    \* assert \A ans \in BestKnapsack(itemset): ans \in ValidKnapsacks(itemset)
    assert BestKnapsack(itemset) \subseteq ValidKnapsacks(itemset)
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "5941852f" /\ chksum(tla) = "34ffa71b")
VARIABLES itemset, pc

vars == << itemset, pc >>

Init == (* Global variables *)
        /\ itemset \in ItemSets
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(BestKnapsack(itemset) \subseteq ValidKnapsacks(itemset), 
                   "Failure of assertion at line 50, column 5.")
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
