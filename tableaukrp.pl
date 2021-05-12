/* A Tableau Implementation for first-order logic; from "First-Order Logic and Automated Theorem Proving" by Melvin Fitting; minor modifications by Dorota Leszczyńska-Jasion */

:- dynamic funcount/1.

:- op(140,fy,neg).
:- op(160,xfy,[and,or,imp,revimp,uparrow,downarrow,notimp,notrevimp]).

/* remove(Item,List,Newlist) :-
	Newlist is the result of removing all occurrences of Item from List.
*/

remove(_,[],[]).
remove(X,[Y | Tail],Newtail) :-
	X == Y,!,
	remove(X,Tail,Newtail).
remove(X,[Y | Tail],[Y | Newtail]) :-
	X \== Y,!,
	remove(X,Tail,Newtail).

/* conjunctive(X) :- X is an alpha formula
*/

conjunctive(_ and _).          %AND
conjunctive(neg(_ or _)).      %NOT OR
conjunctive(neg(_ imp _)).     %not(if A, then B)
conjunctive(neg(_ revimp _)).  %not(A, if B)
conjunctive(neg(_ uparrow _)). %NOT NAND not(at most one)
conjunctive(_ downarrow _).    %NOR (neither nor;Peirce's arrow)
conjunctive(_ notimp _).       %not(if A, then B)
conjunctive(_ notrevimp _).    %not(A, if B)

/* disjunctive(X) :- X is a beta formula
*/

disjunctive(neg(_ and _)).       %NOT AND
disjunctive(_ or _).		 %OR
disjunctive(_ imp _).            %if A, then B
disjunctive(_ revimp _).	 %A, if B
disjunctive(_ uparrow _).        %NAND (at most one;Sheffer's stroke)
disjunctive(neg(_ downarrow _)). %NOT NOR
disjunctive(neg(_ notimp _)).	 %not not if A, then B
disjunctive(neg(_ notrevimp _)). %not not A, if B

/* unary(X) :- X is a double negation, or a negated constant.
*/

unary(neg neg _).
unary(neg true).
unary(neg false).

/* components(X,Y,Z) :- Y and Z are the components of the formula X, as defined in the alpha and beta table.
*/

components(X and Y,X,Y).
components(neg(X and Y),neg X,neg Y).
components(X or Y,X,Y).
components(neg(X or Y),neg X,neg Y).
components(X imp Y,neg X,Y).
components(neg(X imp Y),X,neg Y).
components(X revimp Y,X,neg Y).
components(neg(X revimp Y),neg X,Y).
components(X uparrow Y,neg X,neg Y).
components(neg(X uparrow Y),X,Y).
components(X downarrow Y,neg X,neg Y).
components(neg(X downarrow Y),X,Y).
components(X notimp Y,X,neg Y).
components(neg(X notimp Y),neg X,Y).
components(X notrevimp Y,neg X,Y).
components(neg(X notrevimp Y),X,neg Y).

/* component(X, Y) :- Y is the component of the unary formula X
*/

component(neg neg X, X).
component(neg true, false).
component(neg false, true).

/* universal(X) :- X is a gamma formula
*/

universal(all(_,_)).
universal(neg some(_,_)).

/* existential(X) :- X is a delta formula
*/

existential(some(_,_)).
existential(neg all(_,_)).

/* literal(X) :- X is a literal
*/

literal(X) :-
	\+ conjunctive(X),
	\+ disjunctive(X),
	\+ unary(X),
	\+ universal(X),
	\+ existential(X).

/* atomicfmla(X) :- X is an atomic formula
*/

atomicfmla(X) :-
	literal(X),
	X \= neg _.

/* sub(Term, Variable, Formula, NewFormula) :-	NewFormula is the result of substituting occurrences of Term for each free occurrence of Variable in Formula
*/

sub(Term, Variable, Formula, NewFormula) :-
	sub_(Term, Variable, Formula, NewFormula),!.

sub_(Term, Var, A, Term) :- Var == A.
sub_(_, _, A, A) :- atomic(A).
sub_(_, _, A, A) :- var(A).

sub_(Term, Var, neg X, neg Y) :- sub_(Term, Var, X, Y).

sub_(Term, Var, X and Y, U and V) :-
	sub_(Term, Var, X, U),
	sub_(Term, Var, Y, V).
sub_(Term, Var, X or Y, U or V) :-
	sub_(Term, Var, X, U),
	sub_(Term, Var, Y, V).
sub_(Term, Var, X imp Y, U imp V) :-
	sub_(Term, Var, X, U),
	sub_(Term, Var, Y, V).
sub_(Term, Var, X revimp Y, U revimp V) :-
	sub_(Term, Var, X, U),
	sub_(Term, Var, Y, V).
sub_(Term, Var, X uparrow Y, U uparrow V) :-
	sub_(Term, Var, X, U),
	sub_(Term, Var, Y, V).
sub_(Term, Var, X downarrow Y, U downarrow V) :-
	sub_(Term, Var, X, U),
	sub_(Term, Var, Y, V).
sub_(Term, Var, X notimp Y, U notimp V) :-
	sub_(Term, Var, X, U),
	sub_(Term, Var, Y, V).
sub_(Term, Var, X notrevimp Y, U notrevimp V) :-
	sub_(Term, Var, X, U),
	sub_(Term, Var, Y, V).

sub_(_, Var, all(Var,Y), all(Var,Y)).
sub_(Term, Var, all(X, Y), all(X, Z)) :- sub_(Term, Var, Y, Z).
sub_(_, Var, some(Var, Y), some(Var, Y)).
sub_(Term, Var, some(X, Y), some(X, Z)) :- sub_(Term, Var, Y, Z).

sub_(Term, Var, Functor, Newfunctor) :-
	Functor =.. [F | Arglist],
	sub_list(Term, Var, Arglist, Newarglist),
	Newfunctor =.. [F | Newarglist].

sub_list(Term, Var, [Head | Tail], [Newhead | Newtail]) :-
	sub_(Term, Var, Head, Newhead),
	sub_list(Term, Var, Tail, Newtail).
sub_list(_, _, [], []).

/* instance(F, Term, Ins) :- F is a quantified formula, and Ins is the result of removing the quantifier and replacing all free occurrences of the quantified variable by occurrences of Term
*/

instance(all(X,Y), Term, Z) :- sub(Term, X, Y, Z).
instance(neg some(X,Y), Term, neg Z) :- sub(Term, X, Y, Z).
instance(some(X,Y), Term, Z) :- sub(Term, X, Y, Z).
instance(neg all(X,Y), Term, neg Z) :- sub(Term, X, Y, Z).

/* SKOLEM FUNCTIONS

funcount(N) :- N is the current Skolem function index (funcount defined
as a dynamic procedure!!)

newfuncount(N) :- N is the current Skolem function index, and as a side
effect, the rememebered value is incremented

reset :- the Skolem function index is reset to 1

sko_fun(X, Y) :- X is a list of free variables, and Y is a previously
unused Skolem function symbol applied to those free variables
*/

funcount(1).

newfuncount(N) :-
	funcount(N),
	retract(funcount(N)),
	M is N+1,
	assert(funcount(M)).

reset :- retract(funcount(_)),
	assert(funcount(1)),
	!.

sko_fun(Varlist, Skoterm) :-
	newfuncount(N),
	Skoterm =.. [fun | [N | Varlist]].

/* NOTATED BRANCHES
notation(Notated, Information) :- Notated is a notated branch, and
Information is its associated information
branch(Notated, Branch) :- Notated is a notated branch, and Branch is
its branch part
*/

notation(nb(X,_), X).

branch(nb(_,Y), Y).

/* singlestep(OldTableau, OldQdepth, NewTableau, NewQdepth) :- the application of one tableau rule to OldTableau, with a Q-depth of OldQdepth, will produce the tableau NewTableau, and will change the available Q-depth to NewQdepth
*/

singlestep([OldNotated | Rest], Qdepth, [NewNotated | Rest], Qdepth) :-
	branch(OldNotated, Branch),
	notation(OldNotated, Free),
	member(Formula, Branch),
	unary(Formula),!,
	component(Formula, NewFormula),
	remove(Formula, Branch, TempBranch),
	NewBranch = [NewFormula | TempBranch],
	branch(NewNotated, NewBranch),
	notation(NewNotated, Free).
singlestep([OldNotated | Rest], Qdepth, [NewNotated | Rest], Qdepth) :-
	branch(OldNotated, Branch),
	notation(OldNotated, Free),
	member(Alpha, Branch),
	conjunctive(Alpha),!,
	components(Alpha, AlphaOne, AlphaTwo),
	remove(Alpha, Branch, TempBranch),
	NewBranch = [AlphaOne, AlphaTwo | TempBranch],
	branch(NewNotated, NewBranch),
	notation(NewNotated, Free).
singlestep([OldNotated | Rest], Qdepth, [NewOne, NewTwo | Rest], Qdepth) :-
	branch(OldNotated, Branch),
	notation(OldNotated, Free),
	member(Beta, Branch),
	disjunctive(Beta),!,
	components(Beta, BetaOne, BetaTwo),
	remove(Beta, Branch, TempBranch),
	BranchOne = [BetaOne | TempBranch],
	BranchTwo = [BetaTwo | TempBranch],
	branch(NewOne, BranchOne),
	notation(NewOne, Free),
	branch(NewTwo, BranchTwo),
	notation(NewTwo, Free).
singlestep([OldNotated | Rest], Qdepth, [NewNotated | Rest], Qdepth) :-
	branch(OldNotated, Branch),
	notation(OldNotated, Free),
	member(Delta, Branch),
	existential(Delta),!,
	sko_fun(Free, Term),
	instance(Delta, Term, DeltaInstance),
	remove(Delta, Branch, TempBranch),
	NewBranch = [DeltaInstance | TempBranch],
	branch(NewNotated, NewBranch),
	notation(NewNotated, Free).
singlestep([OldNotated | Rest], OldQdepth, NewTree, NewQdepth) :-
	branch(OldNotated, Branch),
	notation(OldNotated, Free),
	member(Gamma, Branch),
	universal(Gamma),!,
	OldQdepth > 0,
	remove(Gamma, Branch, TempBranch),
	NewFree = [V | Free],
	instance(Gamma, V, GammaInstance),
	append([GammaInstance | TempBranch], [Gamma], NewBranch),
	branch(NewNotated, NewBranch),
	notation(NewNotated, NewFree),
	append(Rest, [NewNotated], NewTree),
	NewQdepth is OldQdepth-1.
singlestep([Notated | OldRest], OldQdepth, [Notated | NewRest], NewQdepth) :-
	singlestep(OldRest, OldQdepth, NewRest, NewQdepth).

/* expand(Tree, Qdepth, Newtree) :- the complete expansion of the tableau Tree, allowing Qdepth applications of the gamma rule, is Newtree */

expand(Tree, Qdepth, Newtree) :-
	singlestep(Tree, Qdepth, TempTree, TempQdepth),!,
	%write(Tree),nl,
	expand(TempTree, TempQdepth, Newtree).
expand(Tree, _, Tree).

/* unify(Term1, Term2) :- Term1 and Term2 are unified with the occurs check (Stirling and Shapiro, "The Art of Prolog")
*/

unify(X,Y) :- var(X), var(Y), X=Y.
unify(X,Y) :- var(X), nonvar(Y), not_occurs_in(X,Y), X=Y.
unify(X,Y) :- var(Y), nonvar(X), not_occurs_in(Y,X), Y=X.
unify(X,Y) :- nonvar(X), nonvar(Y), atomic(X), atomic(Y), X=Y.
unify(X,Y) :- nonvar(X), nonvar(Y), cmpnd(X), cmpnd(Y), term_unify(X,Y).

not_occurs_in(X,Y) :- var(Y), X \== Y.
not_occurs_in(_,Y) :- nonvar(Y), atomic(Y).
not_occurs_in(X,Y) :- nonvar(Y), cmpnd(Y), functor(Y,_,N),
	not_occurs_in(N,X,Y).
not_occurs_in(N,X,Y) :-
	N > 0, arg(N,Y,Arg),
	not_occurs_in(X,Arg),
	N1 is N-1,
	not_occurs_in(N1,X,Y).
not_occurs_in(0,_,_).

term_unify(X,Y) :-
	functor(X,F,N), functor(Y,F,N), unify_args(N,X,Y).

unify_args(N,X,Y) :-
	N>0, unify_arg(N,X,Y), N1 is N-1, unify_args(N1,X,Y).
unify_args(0,_,_).

unify_arg(N,X,Y) :-
	arg(N,X,ArgX), arg(N,Y,ArgY), unify(ArgX,ArgY).

cmpnd(X) :- functor(X,_,N), N>0.

/* closed(Tableau) :- every branch of Tableau can be made to contain a contradiction, after a suitable free variable substitution
*/

closed([Notated | Rest]) :-
	branch(Notated, Branch),
	member(false, Branch),
	closed(Rest).
closed([Notated | Rest]) :-
	branch(Notated, Branch),
	member(X, Branch),
	atomicfmla(X),
	member(neg Y, Branch),
	unify(X, Y),
	closed(Rest).
closed([]).

/* if_then_else(P, Q, R) :- either P and Q, or not P and R
*/

if_then_else(P, Q, _) :- P, !, Q.
if_then_else(_, _, R) :- R.

/* test(X, Qdepth) :- create a complete tableau expansion for neg X, allowing Qdepth applications of the gamma rule. Test for closure
*/

test(X, Qdepth) :-
	reset,
	branch(Notated, [neg X]),
	notation(Notated, []),
	expand([Notated], Qdepth, Tree),
	if_then_else(closed(Tree), yes(Qdepth), no(Qdepth)),
	!,fail.

yes(Qdepth) :-
	write('Podana formuła posiada dowód (w systemie TA) o Q-głębokoci '),
	write(Qdepth),
	write('.'),nl.

no(Qdepth) :-
	write('Podana formuła nie posiada dowodu (w systemie TA) o Q-głębokoci '),
	write(Qdepth),
	write('.'),nl,
	write('Wypróbuj większš Q-głębokoć.').
