nalezy_do_listy(X,[X|_]).
nalezy_do_listy(X,[_|Y]):-
nalezy_do_listy(X,Y).

podzbior([],Y).
podzbior([A|X],Y):-nalezy_do_listy(A,Y),
podzbior(X,Y).


czesc_wspolna([],X,[]).
czesc_wspolna([X|R],Y,[X|Z]):-
nalezy_do_listy(X,Y),!,
czesc_wspolna(R,Y,Z).
czesc_wspolna([X|R],Y,Z):-
czesc_wspolna(R,Y,Z).


suma_zb([],X,X).
suma_zb([X|R],Y,Z):-nalezy_do_listy(X,Y),!,
suma_zb(R,Y,Z).
suma_zb([X|R],Y,[X|Z]):-suma_zb(R,Y,Z).



roznica([],_,[]).
roznica([X|L],Set,[X|Z]):-
not(member(X,Set)),!,
roznica(L,Set,Z).
roznica([_|L],Set,Z):-roznica(L,Set,Z).
