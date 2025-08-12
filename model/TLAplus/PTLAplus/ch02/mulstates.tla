---- MODULE mulstates ----
EXTENDS Integers, TLC, Sequences

ArbitraryNumber == 1..3 \* 1..3
ArbitraryBoolean == BOOLEAN \* {FALSE, TRUE}

SUBSETSet == SUBSET {"a", "b"} \* {{}, {"a"}, {"b"}, {"a", "b"}}
UNIONSet == UNION {{"a"}, {"b"}, {"b", "c"}} \* {"a", "b", "c"}

(*
Error evaluating expression:
Attempted to apply the operator overridden by the Java method
public static tlc2.value.impl.IntervalValue tlc2.module.Integers.DotDot(tlc2.value.impl.IntValue,tlc2.value.impl.IntValue),
but it produced the following error:
Cannot cast tlc2.value.impl.SetOfTuplesValue to tlc2.value.impl.IntValue
*)
\* ArbitraryTuple == {"a", "b", "c"} \X 1..2
ArbitraryTuple == {"a", "b", "c"} \X (1..2) \* {<<"a", 1>>, <<"a", 2>>, <<"b", 1>>, <<"b", 2>>, 
                                            \*  <<"c", 1>>, <<"c", 2>>}
\* \X is not associative
TupleNotIn1 == <<1, 2, 3>> \in (1..3) \X (1..3) \X (1..3)   \* TRUE
TupleNotIn2 == <<1, 2, 3>> \in (1..3) \X ((1..3) \X (1..3)) \* FALSE

ArbitraryStructure1 == [a: {"a", "b"}]            \* {[a |-> "a"], [a |-> "b"]}
ArbitraryStructure2 == [a: {"a", "b"}, b: (1..2)] \* {[a |-> "a", b |-> 1], [a |-> "a", b |-> 2], 
                                                  \*  [a |-> "b", b |-> 1], [a |-> "b", b |-> 2]} 
====