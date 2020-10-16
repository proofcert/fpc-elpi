% based on history meta-interpreter
:- ensure_loaded('meta-co.pl').

:- discontiguous coinductive/2.

:- dynamic automata/3.
:- dynamic accepts/2.
:- dynamic drop/3.
:- dynamic trans/3.
:- dynamic comember/2.
:- dynamic final/1.

% true is X occurs in Xs infinitely oftern. Fail if finte list, loops
% if it does not.
coinductive(comember,2).
comember(X,L) :-
    drop(X,L,L1), comember(X,L1).
drop(H,[H|T],T).
drop(H,[_|T],T1) :- drop(H,T,T1).

% eg. Xs = [1,2,3|Xs], query(comember(2,Xs)).
% Xs = [1, 2, 3|Xs]

% Xs = [1,2,3], query(comember(2,Xs)).
% false.


coinductive(automata,3).
automata([X|T], St, Sts) :-
    trans(St, X, NewSt), automata(T, NewSt,[St|Sts]).
trans(s0, a, s1).
trans(s1, b, s2).
trans(s2, c, s3).
trans(s3, d, s0).
trans(s2, e, s0).
final(s2).


% String accepted by fixed automata  starting with InitSt and with Final
% occurring inf often

% (abcd)* accepted and final s2 occurs infintely often

accepts(String,InitSt) :-
    automata(String,InitSt,Sts),
    final(Final),
    comember(Final,Sts).

%  query((automata(X,s0, States ), comember(s2,States))).
%  X = [a, b, c, d|X],
% States = [s3, s2, s1, s0|States] ;

%query(accepts(String,s0)).
%String = [a, b, c, d|String]
