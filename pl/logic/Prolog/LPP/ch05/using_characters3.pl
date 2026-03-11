/* read in a series of characters ending with * and count the number of vowels */

go(Vowels) :- count(0,Vowels).

count(Oldvowels,Totvowels) :-
  get0(X),process(X,Oldvowels,Totvowels).

process(42,Oldvowels,Oldvowels).
process(X,Oldvowels,Totalvowels):-
  X =\= 42,processChar(X,Oldvowels,New),
  count(New,Totalvowels).

processChar(X,Oldvowels,New) :- vowel(X),
  New is Oldvowels + 1.
processChar(X,Oldvowels,Oldvowels).

vowel(65)./* A */
vowel(69)./* E */
vowel(73)./* I */
vowel(79)./* O */
vowel(85)./* U */
vowel(97)./* a */
vowel(101)./* e */
vowel(105)./* i */
vowel(111)./* o */
vowel(117)./* u */