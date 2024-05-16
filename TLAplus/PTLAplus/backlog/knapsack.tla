------------------------------ MODULE knapsack ------------------------------
EXTENDS TLC, Integers, Sequences
CONSTANTS Capacity, Items, SizeRange, ValueRange
PT == INSTANCE PT

\*Capacity == 7

\*Items == {"a", "b", "c"}
\*ItemParams == [size: 2..4, value: 0..5]
ItemParams == [size: SizeRange, value: ValueRange]
\* ItemSets == [a: ItemParams, b: ItemParams, c: ItemParams]
ItemSets == [Items -> ItemParams]

HardcodedItemSet == [
    a |-> [size |-> 1, value |-> 1],
    b |-> [size |-> 2, value |-> 3],
    c |-> [size |-> 3, value |-> 1]
]

\* sack: item |-> count
KnapsackSize(sack, itemset) ==
    LET size_for(item) == itemset[item].size * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: size_for(item) + acc, Items, 0)

ValidKnapsacks(itemset) ==
    {sack \in [Items -> 0..4]: KnapsackSize(sack, itemset) <= Capacity}

KnapsackValue(sack, itemset) ==
    LET value_for(item) == itemset[item].value * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: value_for(item) + acc, Items, 0)

\* may be multiple best cases
BestKnapsacks(itemset) ==
    LET 
        value(sack) == KnapsackValue(sack, itemset)
        all == ValidKnapsacks(itemset)
        best == CHOOSE best \in all:
                    \A worse \in all \ {best}:
                        value(best) >= value(worse)
    IN {k \in all: value(best) = value(k)}

\* BestKnapsacks(HardcodedItemSet)
\* {[a |-> 1, b |-> 3, c |-> 0]}

\* KnapsackValue([a |-> 1, b |-> 3, c |-> 0], HardcodedItemSet)
\* 10

(*--algorithm knapsack
variables
    itemset \in ItemSets;

begin
    assert BestKnapsacks(itemset) \subseteq ValidKnapsacks(itemset);
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "6d2365f" /\ chksum(tla) = "5af64842")
VARIABLES itemset, pc

vars == << itemset, pc >>

Init == (* Global variables *)
        /\ itemset \in ItemSets
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(BestKnapsacks(itemset) \subseteq ValidKnapsacks(itemset), 
                   "Failure of assertion at line 53, column 5.")
         /\ pc' = "Done"
         /\ UNCHANGED itemset

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Fri Aug 19 13:09:03 CST 2022 by zhoujiagen
\* Created Fri Aug 19 11:48:08 CST 2022 by zhoujiagen
