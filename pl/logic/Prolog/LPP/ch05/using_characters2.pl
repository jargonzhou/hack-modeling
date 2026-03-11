/* output the number of characters (excluding the *) */

go(Total) :- count(0,Total).

count(Oldcount,Result) :-
  get0(X),process(X,Oldcount,Result).

process(42,Oldcount,Oldcount).
process(X,Oldcount,Result) :-
  X =\= 42,New is Oldcount + 1,count(New,Result).