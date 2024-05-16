/* read the first four terms from a specified file and
output them to another specified file, one per line. */

readterms(Infile,Outfile):-
  seeing(S),
  see(Infile),
  telling(T),
  tell(Outfile),
  
  read(T1),write(T1),nl,read(T2),write(T2),nl,
  read(T3),write(T3),nl,read(T4),write(T4),nl,
  
  seen,
  see(S),
  told,
  tell(T).
