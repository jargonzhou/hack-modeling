?-dynamic(position/2).
?-dynamic(orientation/1).

control_robot :- initialise,report,repeat,inputline(L),L=[],!.

inputline(L) :- buildlist(L,[]),reverse(L,L1),writeout(L1),!.

writeout(['']).
writeout(L) :- ((verify(L),X=..L,call(X));(write('Invalid input'),nl)).

buildlist(L,OldL) :- findword(Word,[]),
  (
    (Word=[],L=OldL);
    (Word=[sep],buildlist(L,OldL));
    (Word=[termin|Word1],name(S,Word1),L=[S|OldL]);
    (name(S,Word),buildlist(L,[S|OldL]))
  ).

findword(Word,OldWord) :- get0(X1),repchar(X1,X),
  (
    (terminator(X),Word=[termin|OldWord]);
    (separator(X),((OldWord=[],Word=[sep]);
    Word=OldWord));
    (append(OldWord,[X],New),findword(Word,New))
  ).

separator(32). /* space*/
terminator(10). /* end of line */

repchar(X,New) :- X>=65,X=<90,New is X+32,!.
repchar(Char,Char).

% stop :- write('End of Input'),nl.

verify([H|L]) :- member(H,[forward,back,turn,goto,face,report,stop]).

forward(N,metres) :- 
  retract(position(North,East)),
  orientation(Degrees),radians(Degrees,Rads),
  North1 is North+N*sin(Rads),
  East1 is East+N*cos(Rads),
  assertz(position(North1,East1)),
  write('** New position is '),
  round2dp(North1,North2),round2dp(East1,East2),
  write(North2),write(' metres North and '),
  write(East2),write(' metres East'),nl.

back(N,metres) :- turn(180,degrees,anticlockwise),forward(N,metres).

turn(right) :- turn(90,degrees,clockwise).
turn(left) :- turn(90,degrees,anticlockwise).
turn(round) :- turn(180,degrees,anticlockwise).
turn(N,degrees,clockwise) :- N1 is -1*N, turn(N1,degrees,anticlockwise).
turn(N,degrees,anticlockwise) :- 
  retract(orientation(Current)),
  New is (CurrentCN) mod 360,assertz(orientation(New)),
  write('** New orientation is '),write(New),
  write(' degrees anticlockwise from East'),nl.

goto(North,north,East,east) :- 
  retract(position(_,_)),
  assertz(position(North,East)),
  write('** New position is '),
  write(North),write(' metres North and '),
  write(East),write(' metres East'),nl.

report :- position(North,East),write('** Position is '),
  round2dp(North,North1),round2dp(East,East1),
  write(North1),write(' metres North and '),
  write(East1),write(' metres East'),nl,
  orientation(N),write('** Orientation is '),write(N),
  write(' degrees anticlockwise from East'),nl.

face(N,degrees) :- 
  retract(orientation(_)),
  assertz(orientation(N)),
  write('** New orientation is '),
  write(N),write('degrees anticlockwise from East'),nl.

stop :- write('STOP'),nl,report.

/* N degrees converted to M radians (pi radians=180 degrees) */
radians(N,M) :- M is (3.14159265)*N/180.

round2dp(X,Y) :- Y is round(X*100)/100.

initialise :- 
  retractall(orientation(_)),retractall(position(_,_)),
  assertz(position(0,0)), /* zero metres North and zero metres East */
  assertz(orientation(90)). /* degrees anticlockwise from east*/

/*
?- control_robot.
** Position is 0 metres North and 0 metres East
** Orientation is 90 degrees anticlockwise from East
|: TURN right
** New orientation is 0 degrees anticlockwise from East
|: TURN 30 degrees clockwise
** New orientation is 330 degrees anticlockwise from East
|: TURN round
** New orientation is 150 degrees anticlockwise from East
|: TURN LEFT
** New orientation is 240 degrees anticlockwise from East
|: TURN 140 degrees anticlockwise
** New orientation is 20 degrees anticlockwise from East
|: REPORT
** Position is 0 metres North and 0 metres East
** Orientation is 20 degrees anticlockwise from East
|: FACE 70 degrees
** New orientation is 70 degrees anticlockwise from East
|: STOP
End of Input
true.
*/
