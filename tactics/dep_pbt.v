
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

  %% build_clauses: given a Coq context, creates copy clauses associating
  %% the eigenvariables to fresh logic variables
  % goal-ctx is a list of predicates of the form "decl Var Name Type",
  % representing the assumptions in the current goal as a triplet of a lProlog
  % eigenvariable, a pretty-print name and the type of the assumption. This
  % predicate associates such a list with a list of copy clauses copying each
  % eigenvariable to a fresh (hence the Elpi syntax X_) lProlog logic variable.
  % Morally, this turns universally quantified eigenvariables into existentially
  % quantified logic variables.

  type build_clauses goal-ctx -> list prop -> prop.
  build_clauses [decl Var _Name _Ty] [(copy Var X_ :- !)].
  build_clauses [decl Var _Name _Ty | Ds] [(copy Var X_ :- !)| Cs] :-
    build_clauses Ds Cs.
  %% env_clauses: given a Coq context creates copy clauses associating
  %% an eigenvariable to its type. 
  % As before, the goal context is given as a list of triplets (eigenvariable,
  % name, type). Here, we associate this list to a list of copy clauses that
  % copies each eigenvariable to its type. Indeed, the tactic will be invoked
  % with a list of parameters that are simply eigenvariables: c1, c3, ... With
  % this predicate, we wish to create goals of the intended types.


  type env_clauses goal-ctx -> list prop -> prop.
  env_clauses [decl Var _ Ty] [(copy Var Ty :- !)].
  env_clauses [decl Var _ Ty |L] [(copy Var Ty :- !)|Cs] :-
    env_clauses L Cs.

  %% remove_trm: removes the coercion trm on the argument and returns a list of terms
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
%    coq.say "Specs:" {std.map SpecGoals (t\s\ coq.term->string t s)},
%    coq.say "Spec Vars:" {std.map SpecVars (t\s\ coq.term->string t s)},
%    coq.say "Prog:" {coq.term->string ProgGoal},
%    coq.say "Prop:" {coq.term->string PropGoal},
    std.map SpecGoals (g\t\ check (qgen (qheight N)) (go g t)) SpecVars,
    % coq.say "Proof Term:" {std.map SpecVars (t\s\ coq.term->string t s)},
    % coq.say "Interp" {coq.term->string ProgGoal},
    interp ProgGoal,
    % coq.say "Run" {coq.term->string PropGoal},
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
