From elpi Require Import elpi.
Require Import Arith.
Require Import Coq.Lists.List.
Import ListNotations.
Elpi Tactic pbt.
Elpi Accumulate File "pbt/kernel.mod".
Elpi Accumulate File "pbt/fpc-qbound.mod".
Elpi Accumulate File "pbt/fpc-pair.mod".

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

  solve [trm Spec, trm Prog, int N, trm Monitor_] [goal Ctx _Ev Ty _Who] _OutGoals :-
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
    check (qgen (qheight N)) (go SpecGoal),
    interp ProgGoal,
    % Use of monitor variable should be deprecated
    % (Cs => copy Monitor Result),
    % coq.say "Trying:" {coq.term->string Result}, 
    not (interp PropGoal),
    coq.say "Counterexample:" {coq.term->string PropGoal}.
%qsize
  solve [str "size", trm Spec, trm Prog, int N, trm Monitor_] [goal Ctx _Ev Ty _Who] _OutGoals :-
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
    check (qgen (qsize N N0_)) (go SpecGoal),
    interp ProgGoal,
    % (Cs => copy Monitor Result),
    % coq.say "Trying:" {coq.term->string Result}, 
    not (interp PropGoal),
    coq.say "Counterexample:" {coq.term->string PropGoal}.

%pairing
solve [str "pair", trm Spec, trm Prog, int N, int S, trm Monitor_] [goal Ctx _Ev Ty _Who] _OutGoals :-
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
    check (pair (qgen (qheight N)) (qgen (qsize S S2_ ))) (go SpecGoal),
    interp ProgGoal,
    % (Cs => copy Monitor Result),
    % coq.say "Trying:" {coq.term->string Result}, 
    not (interp PropGoal),
    coq.say "Counterexample:" {coq.term->string PropGoal}.
}}.
Elpi Typecheck.
