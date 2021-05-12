element(X,[X|_]).
element(X,[_|Ogon]) :- element(X,Ogon).

polacz([],L,L).
polacz([X|L1],L2,[X|L3]):-polacz(L1,L2,L3).

dlugosc([],0).
dlugosc([_|O],N):-dlugosc(O,N1),N is N1+1.


odwracanie([],[]).
odwracanie([A|B],C):- odwracanie(B,D),append(D,[A],C).

poczatek([],[_|_]).
poczatek([H1|T1], [H2|T2]) :- H1=H2, poczatek(T1,T2).


poczatek2([],_).
poczatek2([H1|T1],[H1|T2]):-poczatek2(T1,T2).

ostatni([H], H).
ostatni([_|T], O) :- ostatni(T, O).


max([X], X).
max([H|T], X) :- max(T, X1), X1 > H, X is X1.
max([H|T], X) :- max(T, X1), X1 < H, X is H.

max2([], 'Brak elementów w liście').
max2(L, W) :- sort(L, L1), last(L1, W).

rosnacy([_]).
rosnacy([G|[H|T]]) :- G < H, rosnacy([H|T]).


nty(X,[X|_],1).
nty(X,[_|T],N) :- nty(X,T,N1), N is N1+1.



h(104).
i(105).
