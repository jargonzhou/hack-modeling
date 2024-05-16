/* copy characters input (as a single line) at the user's terminal to a specified file, 
until the character ! is entered */

copychars(Outfile) :- 
  telling(T),
  tell(Outfile),

  copy_characters,
  
  told,
  tell(T).
  
copy_characters :- get0(N),process(N).

/* 33 is ASCII value of character ! */
process(33).
process(N) :- N =\= 33,put(N),copy_characters.