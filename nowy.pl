parzysty([X,Y]).
parzysty([X,Y|T]):-parzysty(T).




lubi(jan, tatry).
 lubi(jan, beskidy).
 lubi(jerzy, beskidy).
 lubi(jerzy, bieszczady).
 lubi(józef, sudety).
 lubi(justyna, gświętokrzyskie).
 bratniadusza(X, Y) :- lubi(X, S), lubi(Y, S), X \= Y.


 a(0).
  a(X) :- a(Y), X is Y+1.



przedostatni([X],L).
przedostatni([_,O,Y],L):- przedostatni(O,L).
