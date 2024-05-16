readlineF(File) :-
  see(File),repeat,inputline(L),L=[end_of_file],!,seen.

inputline(L) :- buildlist(L,[]),reverse(L,L1),writeout(L1),!.

writeout([]).
writeout([end_of_file]).
writeout(L) :- write('Sentence: '),write(L),nl.

/*
?- readlineF('dickens.txt').
Sentence: [marley,was,dead,to,begin,with]
Sentence: [there,is,no,doubt,whatever,about,that]
Sentence: [the,register,of,his,burial,was,signed,by,the,clergyman,the,clerk,the,
undertaker,and,the,chief,mourner]
Sentence: [scrooge,signed,it]
Sentence: [and,scrooge's,name,was,good,upon,'change,for,anything,he,chose,to,
put,his,hand,to]
Sentence: [old,marley,was,as,dead,as,a,door-nail]
true.
*/

readlineF2(File,Outfile) :-
  see(File),tell(Outfile),repeat,inputline2(L),
  L=[end_of_file],!,told,seen.

inputline2(L) :- buildlist(L,[]),reverse(L,L1),writeout2(L1),!.

writeout2([]).
writeout2([end_of_file]).
writeout2(L):-writeq(L),write('.'),nl.

/*
?- readlineF2('dickens.txt','newdickens.txt').
true.
*/

buildlist(L,OldL) :- findword(Word,[]),
  (
    (Word=[],L=OldL);
    (Word=[end_of_file],L=[end_of_file]);
    (Word=[sep],buildlist(L,OldL));
    (Word=[termin|Word1],name(S,Word1),L=[S|OldL]);
    (name(S,Word),buildlist(L,[S|OldL]))
  ).

findword(Word,OldWord) :-get0(X1),repchar(X1,X),
  (
    (terminator(X),Word=[termin|OldWord]);
    (separator(X),((OldWord=[],Word=[sep]);
    Word=OldWord));
    (X<0,Word=[end_of_file]);
    (append(OldWord,[X],New),findword(Word,New))
  ).

/* upper case to lower case */
repchar(X,New) :- X>=65,X=<90, New is X+32,!.
repchar(Char,Char).

separator(10). /* end of line */
separator(32). /* space*/
separator(44). /* comma */
separator(58). /* colon */

terminator(46). /* full stop */
terminator(33). /* exclamation mark */
terminator(63). /* question mark */