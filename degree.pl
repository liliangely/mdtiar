:-op(140, fy, neg).
:-op(160, xfy, [and, or, imp, revimp, uparrow, downarrow, notimp, notrevimp]).

d(p,0):-!.
d(q,0):-!.
d(r,0):-!.

d(Z,N):-Z=X and Y, d(X,N1), d(Y,N2), N is N1+N2+1,!.

d(Z,N):-Z=X or Y, d(X,N1), d(Y,N2), N is N1+N2+1,!.

d(Z,N):-Z=X imp Y, d(X,N1), d(Y,N2), N is N1+N2+1,!.

d(Z,N):-Z=X revimp Y, d(X,N1), d(Y,N2), N is N1+N2+1,!.

d(Z,N):-Z= neg X, d(X,N1), N is N1+1,!.
