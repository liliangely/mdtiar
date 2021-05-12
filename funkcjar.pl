:-op(140, fy, neg).
:-op(160, xfy, [and, or, imp, revimp, uparrow, downarrow, notimp, notrevimp]).

r(p,0):-!.
r(q,0):-!.
r(r,0):-!.
r(s,0):-!.
r(neg p,0);-!.
r(neg q,0);-!.
r(neg r,0);-!.
r(neg s,0);-!.

r(A,B):-A= verum, r(verum, B1), B is 0.
r(A,B):-A= falsum, r(verum, B1), B is 0.
r(A,B):-A= neg(verum), r(verum, B1), B is 1.
r(A,B):-A= neg(falsum), r(verum, B1), B is 1.

r(A,B):-A= neg neg X, r(X,B1), B is B1+1.

r(A,B):-A= X and Y, r(X,B1), r(Y,B2), B is B1+B2+1.
r(A,B):-A= neg(X or Y), r(X,B1), r(Y,B2), B is B1+B2+1.
r(A,B):-A= neg(X imp Y), r(X,B1), r(Y,B2), B is B1+B2+1.
r(A,B):-A= neg(X reimp Y), r(X,B1), r(Y,B2), B is B1+B2+1.
r(A,B):-A= X downarrow Y, r(X,B1), r(Y,B2), B is B1+B2+1.
r(A,B):-A= neg(X uparrow Y), r(X,B1), r(Y,B2), B is B1+B2+1.

r(A,B):-A= neg(X and Y), r(X,B1), r(Y,B2), B is B1+B2+1.
r(A,B):-A= X or Y, r(X,B1), r(Y,B2), B is B1+B2+1.
r(A,B):-A= X imp Y, r(X,B1), r(Y,B2), B is B1+B2+1.
r(A,B):-A= X reimp Y, r(X,B1), r(Y,B2), B is B1+B2+1.
r(A,B):-A= neg(X downarrow Y), r(X,B1), r(Y,B2), B is B1+B2+1.
r(A,B):-A= X uparrow Y, r(X,B1), r(Y,B2), B is B1+B2+1.

