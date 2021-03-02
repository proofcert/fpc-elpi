(* AM: generalize to other fpc: could use more parametrization
in preprocess 

- qheight is the default (same call)
- can do qsize or pairing of height and size

    call dep_pbt size 10 
*)
From elpi Require Import elpi.

Elpi Tactic dep_pbt.
Elpi Accumulate File "pbt/dep-kernel.mod".
Elpi Accumulate File "pbt/fpc-qbound.mod".
Elpi Accumulate File "pbt/fpc-pair.mod".
Elpi Accumulate lp:{{
  type build_clauses goal-ctx -> list prop -> prop.
  build_clauses [decl Var _Name _Ty] [(copy Var X_ :- !)].
  build_clauses [decl Var _Name _Ty | Ds] [(copy Var X_ :- !)| Cs] :-
    build_clauses Ds Cs.

  type env_clauses goal-ctx -> list prop -> prop.
  env_clauses [decl Var _ Ty] [(copy Var Ty :- !)].
  env_clauses [decl Var _ Ty |L] [(copy Var Ty :- !)|Cs] :-
    env_clauses L Cs.

  type remove_trm list argument -> list term -> prop.
  remove_trm [trm A] [A].
  remove_trm [trm A | R] [A|R'] :- remove_trm R R'.

  %          +   +     -   -     -
  % type preprocess goal-ctx -> list argument -> list term -> ? -> ? -> prop.
  preprocess Ctx SpecT Spec  Cs Progs :-
    remove_trm SpecT Spec,
    build_clauses Ctx Cs,
    env_clauses Ctx Progs.
  
  % default fpc: height
solve [int N, trm Prog | SpecT] [goal Ctx _Ev Goal _] _OutGoals :-
        preprocess Ctx SpecT Spec Cs Progs,
        (Progs => (std.map Spec (x\ y\ copy x y) SpecTypes,
    copy Prog ProgType)),
    (Cs => (std.map SpecTypes (x\y\ copy x y) SpecGoals,
    std.map Spec (x\y\ copy x y) SpecVars,
    copy ProgType ProgGoal,
    copy Goal PropGoal)),
 
    std.map SpecGoals (g\t\ check (qgen (qheight N)) (go g t)) SpecVars,
    interp ProgGoal,
    not (interp PropGoal),
    coq.say "Counterexample:" {coq.term->string ProgGoal}.
% qsize
solve [str "size", int N, trm Prog | SpecT] [goal Ctx _Ev Goal _] _OutGoals :-
      preprocess Ctx SpecT Spec Cs Progs,
        
        (Progs => (std.map Spec (x\ y\ copy x y) SpecTypes,
    copy Prog ProgType)),
    (Cs => (std.map SpecTypes (x\y\ copy x y) SpecGoals,
    std.map Spec (x\y\ copy x y) SpecVars,
    copy ProgType ProgGoal,
    copy Goal PropGoal)),
 
    std.map SpecGoals (g\t\ check (qgen (qsize N M_)) (go g t)) SpecVars,
    interp ProgGoal,
    not (interp PropGoal),
    coq.say "Counterexample:" {coq.term->string ProgGoal}.

    
% pair
solve [str "pair", int N, int S, trm Prog | SpecT] [goal Ctx _Ev Goal _] _OutGoals :-
      preprocess Ctx SpecT Spec Cs Progs,
        
        (Progs => (std.map Spec (x\ y\ copy x y) SpecTypes,
    copy Prog ProgType)),
    (Cs => (std.map SpecTypes (x\y\ copy x y) SpecGoals,
    std.map Spec (x\y\ copy x y) SpecVars,
    copy ProgType ProgGoal,
    copy Goal PropGoal)),
 
    std.map SpecGoals 
       (g\t\ check (pair (qgen (qheight N)) (qgen (qsize S S2_ )))
                  (go g t)) SpecVars,
    interp ProgGoal,
    not (interp PropGoal),
    coq.say "Counterexample:" {coq.term->string ProgGoal}.        
}}.
Elpi Typecheck.
