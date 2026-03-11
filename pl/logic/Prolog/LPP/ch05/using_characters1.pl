/* read in a series of characters from the keyboard finishing with * 
and to output their corresponding ASCII values one per line */

readin :- get0(X), process(X).

process(42). /* * */
process(X) := x =\= 42, write(X), nl, readin.
