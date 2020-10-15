From elpi Require Import elpi.
Require Import Arith List. Import ListNotations.
Require Import Coq.Lists.List.

Elpi Tactic prolog.
Elpi Accumulate File "pbt/src/kernel.mod".
Elpi Accumulate File "pbt/src/fpc-qbound.mod".
Elpi Accumulate File "pbt/src/fpc-pair.mod".

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

  solve [trm Spec, int N] [goal Ctx _Ev _Ty _Who] _OutGoals :-
    build_clauses Ctx Cs,
    env_clauses Ctx Progs,
    (Progs => ( copy Spec SpecType)),
    (Cs => (copy SpecType SpecGoal)),
    coq.say "Goal:" {coq.term->string SpecGoal},
    check (qgen (qheight N)) (go SpecGoal).
  
    
}}.
Elpi Typecheck.
Elpi Bound Steps 10000.


 Inductive ordered : list nat -> Prop :=
onl : ordered []
| oss : forall x : nat, ordered [x]
| ocn : forall (x y : nat) (l : list nat),
     ordered (y :: l) -> x <= y -> ordered (x :: y :: l).

 Goal ordered [0;1;2;6].
   Fail elpi prolog 10.
