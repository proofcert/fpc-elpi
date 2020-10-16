:- use_module(library(coinduction)).

:- coinductive p/1.

p([1|T]) :- p(T).


:- coinductive from/2.
from(N, [N|T]) :- from(s(N), T).

% :- from(0,_). %loops, why?
:- coinductive stream/1.
stream([H | T]) :-
    num(H), stream(T).

num(0).
num(s(N)) :- num(N).

:- coinductive cmem/2.
cmem( H, [ H | _ ] ).
cmem( H, [ _ | T ] ) :- cmem( H, T ).

%  cmem(0,[s(z),0]). % true
%  X = [0|X],cmem(a,X). %true: anything member of a inf list

% called comember/2, which is true if and only if the desired element
% occurs an infnite number of times in the list.

drop( H, [ H | T ], T ).
drop( H, [ _ | T ], T1 ) :- drop( H, T, T1 ).

:- coinductive comember/2.
comember( X, L ) :-
    drop( X, L, L1 ), comember( X, L1 ).

% X = [ 1, 2, 3 | X ], comember( 2, X ). yes
% X = [ 1, 2, 3 | X ], comember( 4, X ). loops
%   X = [ 1, 2, 3], comember( E, X ). fails

%--------------------------------


%:-  stream([0, s(0), s(s(0)) | T ]).
% TODO: some of the bewdyr examples

% from Luke's thesis p.77
% does not seem to work in SWI
:- coinductive automata/2.
automata([X|T], St) :- trans(St, X, NewSt), automata(T, NewSt).
trans(s0, a, s1).
trans(s1, b, s2).
trans(s2, c, s3).
trans(s3, d, s0).
trans(s2, e, s0).
final(s2).

% :- automata(X, s0), comember(s2, X).
:- coinductive bin/1.
bin([0|T]) :- bin(T).
bin([1|T]) :- bin(T).

:-  X = [1|X] , bin(X).
% contrary to paper yap bin(X) does not retun  X = [1|X]. (df)

				% maxlist, example from Ancona should prove - Os = [1|Os], maxList(Os,2). but it does not

max(A,B,Max) :-
	(A < B -> Max = B; Max = A).
mmax(1,2,2).
:- coinductive maxList/2.
maxList([X],X).
maxList([X:L],Z) :-
	maxList(L,Y),mmax(X,Y,Z).