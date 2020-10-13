From elpi Require Import elpi.

Elpi Tactic dep_pbt.
Elpi Accumulate File "pbt/src/dep-kernel.mod".
Elpi Accumulate File "pbt/src/fpc-qbound.mod".
Elpi Accumulate lp:{{
  %% build_clauses: given a Coq context, creates copy clauses associating
  %% the eigenvariables to fresh logic variables
  type build_clauses goal-ctx -> list prop -> prop.
  build_clauses [decl Var _Name _Ty] [(copy Var X_ :- !)].
  build_clauses [decl Var _Name _Ty | Ds] [(copy Var X_ :- !)| Cs] :-
    build_clauses Ds Cs.
  %% env_clauses: given a Coq context creates copy clauses associating
  %% an eigenvariable to its type
  type env_clauses goal-ctx -> list prop -> prop.
  env_clauses [decl Var _ Ty] [(copy Var Ty :- !)].
  env_clauses [decl Var _ Ty |L] [(copy Var Ty :- !)|Cs] :-
    env_clauses L Cs.
  %% remove_trm: removes the coercion trm and returns a list of terms
  remove_trm [trm A] [A].
  remove_trm [trm A | R] [A|R'] :- remove_trm R R'.
  solve [int N, trm Prog | SpecT] [goal Ctx _Ev Ty _Who] _OutGoals :-
    remove_trm SpecT Spec,
    build_clauses Ctx Cs,
    env_clauses Ctx Progs,
    (Progs => (std.map Spec (x\ y\ copy x y) SpecTypes,
    copy Prog ProgType)),
    (Cs => (std.map SpecTypes (x\y\ copy x y) SpecGoals,
    std.map Spec (x\y\ copy x y) SpecVars,
    copy ProgType ProgGoal,
    copy Ty PropGoal)),
    coq.say "Specs:" {std.map SpecGoals (t\s\ coq.term->string t s)},
    coq.say "Spec Vars:" {std.map SpecVars (t\s\ coq.term->string t s)},
    coq.say "Prog:" {coq.term->string ProgGoal},
    coq.say "Prop:" {coq.term->string PropGoal},
    std.map SpecGoals (g\t\ coq.say "calling" g t, check (qgen (qheight N)) (go g t)) SpecVars,
    coq.say "Proof Term:" {std.map SpecVars (t\s\ coq.term->string t s)},
    coq.say "Interp" {coq.term->string ProgGoal},
    interp ProgGoal,
    coq.say "Got" {coq.term->string ProgGoal},
    not (interp PropGoal),
    coq.say "Cex:" PropGoal.
}}.
Elpi Typecheck.