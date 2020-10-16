% automata over different LTS

:- ensure_loaded('meta-co.pl').
:- discontiguous final/2.
:- discontiguous trans/4.
:- discontiguous coinductive/2.

:- dynamic automata/4.
:- dynamic accepts/3.
:- dynamic drop/3.
:- dynamic trans/3.
:- dynamic comember/2.
:- dynamic final/2.
:- dynamic is_aut/2.
:- dynamic not_sim/2.

coinductive(comember,2).
comember(X,L) :-
    drop(X,L,L1), comember(X,L1).
drop(H,[H|T],T).
drop(H,[_|T],T1) :- drop(H,T,T1).


coinductive(automata,4).

accepts(String,InitSt,Trans) :-
    automata(String,InitSt,Trans,Sts),
    final(Trans,Final),
    comember(Final,Sts).


automata([X|T], St, Trans, Sts) :-
    trans(Trans, St, X, NewSt),
    automata(T, NewSt,Trans,[St|Sts]).

% graph g1
trans(g1, s0, a, s1).
trans(g1, s1, b, s2).
trans(g1, s2, c, s3).
trans(g1, s3, d, s0).
trans(g1, s2, e, s0).
final(g1, s2).

% graph g2, 
trans(g2, s0, a, s1).
trans(g2, s1, b, s2).
%trans(g2, s2, c, s3).
%trans(g2, s3, d, s0).
trans(g2, s2, e, s0).
final(g2, s2).

is_aut(g1,s0).
is_aut(g2,s0).

not_sim(A1,A2) :-
    is_aut(g1,InitSt1),
    is_aut(g2,InitSt2),
    accepts(String1,InitSt1,A1),
%    not(accepts(String,InitSt2,A2)). % not not-handled by the meta
    accepts(String2,InitSt2,A2),
    not(String1 =  String2).				
    
