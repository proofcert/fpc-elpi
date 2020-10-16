% metainterpreter with depth-first history mechanism for "coinduction"
:- discontiguous coinductive/2.
query( Goal ) :-
    solve( [], Goal ).
solve( Hypothesis, ( Goal1, Goal2 ) ) :-
    !,
    solve( Hypothesis, Goal1 ),
    solve( Hypothesis, Goal2 ).
solve( _ , Atom ) :-
    builtin( Atom ),
    !,
    Atom.
solve( Hypothesis, Atom ) :-
    coinductive( Atom ),
    member( Atom, Hypothesis ).
solve( Hypothesis, Atom ) :-
    coinductive( Atom ),
    !,
    clause( Atom, Atoms ),
    solve( [ Atom | Hypothesis ], Atoms ).

solve( Hypothesis, Atom ) :-
    %inductive( Atom ),
    clause( Atom, Atoms ),
    solve( Hypothesis, Atoms ).

inductive( Atom ) :-
    Atom \= ( _, _ ),
    \+ builtin( Atom ),
    functor( Atom, Predicate, Arity ),
    inductive( Predicate, Arity ).
coinductive( Atom ) :-
    Atom \= ( _, _ ),
    \+ builtin( Atom ),
    functor( Atom, Predicate, Arity ),
    coinductive( Predicate, Arity ).

builtin( _ = _ ).
builtin( true ).
builtin( _ is _ ).
builtin( _ > _ ).
builtin( _ < _ ).
builtin(\+ _).
builtin(not(_G)).
