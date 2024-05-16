sentence([s1,both,V,NP1,Noun1,NP2,Noun2])
-->noun_phrase(NP1,_,Noun1),verb(both,V),
    noun_phrase(NP2,_,Noun2),{assertz(wordlist(verb,both,V))}.
sentence([s2,Plurality,V,NP1,Noun1,NP2,Noun2])
-->noun_phrase(NP1,Plurality,Noun1),
    verb(Plurality,V),noun_phrase(NP2,_,Noun2),
    {assertz(wordlist(verb,Plurality,V))}.
sentence([s3,both,V,NP1,Noun1])
-->noun_phrase(NP1,_,Noun1),
    verb(both,V),{assertz(wordlist(verb,both,V))}.
sentence([s4,Plurality,V,NP1,Noun1])
-->noun_phrase(NP1,Plurality,Noun1),
    verb(Plurality,V),{assertz(wordlist(verb,Plurality,V))}.

noun_phrase(np1,Plurality,N)
-->determiner,adjective_sequence,noun(Plurality,N).
noun_phrase(np2,Plurality,N)
-->determiner,noun(Plurality,N).
noun_phrase(np3,Plurality,N)
-->noun(Plurality,N).

noun(singular,X)
-->[X],{member(X,[cat,mat,man,boy,dog])}.
noun(plural,X)
-->[X],{member(X,[cats,mats,men,boys,dogs])}.
         
adjective_sequence
-->adjective,adjective_sequence.
adjective_sequence
-->adjective.

verb(both,X)
-->[X],{member(X,[sat,saw,took,will_see])}.
verb(singular,X)
-->[X],{member(X,[hears,sees])}.
verb(plural,X)
-->[X],{member(X,[hear,see])}.

determiner-->[the].
determiner-->[a].
determiner-->[an].

adjective-->[X], {member(X,[large,small,brown,orange,green,blue])}.

/* processor */

process(File):-
  see(File),repeat,read(S),proc(S),S=end_of_file,!,
  seen.

proc(end_of_file).
proc([]).
proc(S) :- write('Sentence: '),write(S),nl,proc2(S).

proc2(S) :- phrase(sentence(L1),S),write('Structure: '),
  write(L1),nl,nl,!.
proc2(S) :- write('Invalid sentence structure'),nl,nl.


/*
?-process('sentences.txt').

?-proc([the,large,green,men,see,a,small,blue,dog]).
Sentence: [the, large, green, men, see, a, small, blue, dog]
Structure: [s2, plural, see, np1, men, np1, dog]

true

?-proc([the,man]).
Sentence: [the, man]
Invalid sentence structure

true
*/