Linked lists.

---- MODULE LL ----
CONSTANT NULL
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE TLC
LOCAL INSTANCE FiniteSets

PointerMaps(Nodes) == [Nodes -> Nodes \union {NULL}]

Range(f) == {f[x]: x \in DOMAIN f}

isLL(PointerMap) ==
    LET 
        nodes == DOMAIN PointerMap
        all_seqs == [1..Cardinality(nodes) -> nodes]
    IN \E ordering \in all_seqs:
        \* each node points to the next node in the ordering
        /\ \A i \in 1..Len(ordering)-1: PointerMap[ordering[i]] = ordering[i+1]
        /\ nodes \subseteq Range(ordering)


LL(Nodes) == 
    IF NULL \in Nodes THEN Assert(FALSE, "NULL cannot be in Nodes")
    ELSE 
        LET 
            node_subsets == (SUBSET Nodes \ {{}})
            pointer_maps_sets == {PointerMaps(subn): subn \in node_subsets}
            all_pointer_maps == UNION pointer_maps_sets
        IN {pm \in all_pointer_maps: isLL(pm)}

Ring(ll) == (DOMAIN ll = Range(ll))
First(ll) ==
    IF Ring(ll)
    THEN CHOOSE node \in DOMAIN ll: TRUE
    ELSE CHOOSE node \in DOMAIN ll: node \notin Range(ll)

Cyclic(ll) == NULL \notin Range(ll)
====