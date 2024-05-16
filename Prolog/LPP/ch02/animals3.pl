/* Animals Program 3 */
dog(fido). large(fido).
cat(mary). large(mary).
dog(rover). dog(jane).
dog(tom). large(tom). cat(harry).
dog(fred). dog(henry).
cat(bill). cat(steve).
small(henry). large(fred).
large(steve). large(jim).
large(mike).

large_animal(X) :- dog(X),large(X).
large_animal(Z) :- cat(Z),large(Z).

/* As Animals Program 2 but with the additional rules given below */
/* chases is a predicate with two arguments*/
chases(X,Y) :-
  dog(X),cat(Y),
  write(X),write(' chases '),write(Y),nl.
/* go is a predicate with no arguments */
go :- chases(A,B).