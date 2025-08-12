---------------------- MODULE BNFGrammars ----------------------
(************************************************************)
(* P.184/202                                                *)
(************************************************************)
EXTENDS TLC
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

--------------------------------------------------------------
(* Operators for defining sets of tokens *)
Symbols == <<"a", "b">>
OneOf(s) == {<<s[i]>> : i \in DOMAIN s}
\* tok(s) == {<<s>>}
\* Tok(S) == {<<s>> : s \in S}

(* Operators for defining languages *)
\* Nil == {<<>>}
\* L & M == {s \o t : s \in L, t \in M}

\* TEST == [](Len("abc") = 3)
TEST == LET i == CHOOSE idx \in 1..Len(Symbols) : TRUE IN
            /\ Print(i, TRUE)
            /\ Print(Symbols[i], TRUE)
            /\ <<Symbols[i]>> \in OneOf(Symbols)
--------------------------------------------------------------
THEOREM TEST => [](1=1)
==============================================================