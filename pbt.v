From elpi Require Import elpi.
Require Import Arith List. Import ListNotations.
Require Import Coq.Lists.List.

Elpi Tactic pbt.
Elpi Accumulate File "pbt/src/kernel.mod".
Elpi Accumulate File "pbt/src/fpc-qbound.mod".
Elpi Accumulate lp:{{
  %% build_clauses: given a Coq context, creates copy clauses associating
  %% the eigenvariables to fresh logic variables
  type build_clauses goal-ctx -> list prop -> prop.
  build_clauses [decl Var _Name _Ty] [(copy Var X_ :- !)].
  build_clauses [decl Var _Name _Ty | Ds] [(copy Var X_ :- !)| Cs] :-
    build_clauses Ds Cs.
  %% env_type: given a Coq context and an eigenvariable, returns the
  %% type of that eigenvariable
  type env_type goal-ctx -> term -> term -> prop.
  env_type [decl Var _ Ty|_] Var Ty.
  env_type [decl _ _ _|L] Var Ty :- env_type L Var Ty.
  %% env_clauses: given a Coq context creates copy clauses associating
  %% an eigenvariable to its type
  type env_clauses goal-ctx -> list prop -> prop.
  env_clauses [decl Var _ Ty] [(copy Var Ty :- !)].
  env_clauses [decl Var _ Ty |L] [(copy Var Ty :- !)|Cs] :-
    env_clauses L Cs.

  solve [trm Spec, trm Prog, int N, trm Monitor] [goal Ctx _Ev Ty _Who] _OutGoals :-
    build_clauses Ctx Cs,
    env_clauses Ctx Progs,
    (Progs => ( copy Spec SpecType,
    copy Prog ProgType)),
    (Cs => (copy SpecType SpecGoal,
    copy ProgType ProgGoal,
    copy Ty PropGoal)),
    coq.say "Spec:" {coq.term->string SpecGoal},
    coq.say "Prog:" {coq.term->string ProgGoal},
    coq.say "Prop:" {coq.term->string PropGoal},
    % coq.say "0",
    check (qgen (qheight N)) (go SpecGoal),
    % coq.say "a" SpecGoal,
    interp ProgGoal,
    % coq.say "b",
    (Cs => copy Monitor _Result),
    % coq.say "Result:" Result, 
    not (interp PropGoal),
    coq.say "Cex:" {coq.term->string PropGoal},
    coq.say "Explain:" true. %was Cs
}}.
Elpi Typecheck.
(* Elpi Query lp:{{not (interp {{rev [] []}})}}. *)
(* Elpi Trace. *)
Elpi Bound Steps 100000.

