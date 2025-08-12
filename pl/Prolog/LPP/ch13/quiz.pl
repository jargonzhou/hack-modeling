?-dynamic(title/1).
?-dynamic(question/3).
?-dynamic(range/3).
?-dynamic(myscore/2).

/* setup */

setup :-
  see('quiz1.txt'),readin,seen,write('Setup completed'),nl.

readin :- read(Title),assertz(title(Title)),readqs.

readqs :- repeat,read(Qtext),process(Qtext),
  Qtext=endquestions,readranges.

process(endquestions) :- !.
process(Qtext) :- proc2([],Anslist,-9999,Maxscore),
  assertz(question(Qtext,Anslist,Maxscore)).

proc2(Anscurrent,Anslist,Maxsofar,Maxscore) :- read(Ans),
  (
    (Ans=end,Anslist=Anscurrent,Maxscore=Maxsofar,!);
    (read(Score),append(Anscurrent,[ans(Ans,Score)], Ansnew),Maxnew is max(Maxsofar,Score),
      proc2(Ansnew,Anslist,Maxnew,Maxscore))
  ).

readranges :-
  repeat,read(First),proc(First),First=endmarkscheme.

proc(endmarkscheme) :- !.
proc(First) :- read(Last),read(Feedback), assertz(range(First,Last,Feedback)).

/* run */

runquiz :- 
  retractall(myscore(_,_)),assertz(myscore(0,0)),
  title(T),write(T),nl,nl,
  askq.

askq :- question(Qtext,Anslist,Maxscore),
  write(Qtext),nl,
  write('Possible answers are '),genanswers(Anslist),
  requestanswer(Anslist,Maxscore),fail.
askq :- myscore(M,Maxtotal),
  write('Your total score is '),write(M),write('points'),
  write(' out of a possible '),write(Maxtotal),nl,
  range(First,Last,Feedback),M>=First,M=<Last,
  write(Feedback),nl,nl,nl.
  
genanswers([ans(A,_)]) :- write('and '),write(A),nl,!.
genanswers([ans(A,_)|L]) :- write(A),write(', '),
genanswers(L).

requestanswer(Anslist,Maxscore) :- 
  write('Enter your answer'),nl,
  readline(Answer),
  (
    (member(ans(Answer,Score),Anslist),
    usescore(Score,Maxscore),!);
    (write('That is not a valid answer - try again!'),nl,
    requestanswer(Anslist,Maxscore))
  ).

usescore(Score,Maxscore) :- 
  write('You have scored '),write(Score),
  write(' points'),
  write(' out of a possible '),write(Maxscore),nl,nl,
  retract(myscore(Old,Oldtotal)),
  New is OldCScore,Newtotal is OldtotalCMaxscore,
  assertz(myscore(New,Newtotal)).

readline(S) :- readline2([],L),name(S,L),!.

readline2(Lcurrent,Lfinal) :- get0(X),
  (
    (X=10,Lfinal=Lcurrent);
    (append(Lcurrent,[X],Lnew),readline2(Lnew,Lfinal))
  ).

/*
?- setup.
?- runquiz.
Are you a genius? Answer our quiz and find out!
What is the name of this planet?
Possible answers are Earth, The Moon, and John
Enter your answer
|: John
You have scored 0 points out of a possible 20
What is the capital of Great Britain?
Possible answers are America, Paris, London, and Moscow
Enter your answer
|: London
You have scored 50 points out of a possible 50
In which country will you find the Sydney Opera House?
Possible answers are London, Toronto, The Moon, Australia, and Germany
Enter your answer
|: Toronto
You have scored 4 points out of a possible 10
Your total score is 54 points out of a possible 80
You need to do some more reading
true .
*/