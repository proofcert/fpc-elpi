From elpi Require Import elpi.

Elpi Tactic dep_pbt.
Elpi Accumulate File "pbt/src/dep-kernel.mod".
Elpi Accumulate File "pbt/src/fpc-qbound.mod".
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
  remove_trm [trm A] [A].
  remove_trm [trm A | R] [A|R'] :- remove_trm R R'.
  solve [int N, trm Prog | SpecT] [goal Ctx _Ev Goal _] _OutGoals :-
    remove_trm SpecT Spec,
    build_clauses Ctx Cs,
    env_clauses Ctx Progs,
    %% First copy: assume the clauses copying the context's eigenvariables to
    %% their types. Then, apply the replacement to the terms given as
    %% specification and program. Thus: if the specification is [c1], the program [c3]
    %% and the context is ["c1: list nat", "c2: list nat", "c3: rev c1 c2"], we will output
    %% [list nat] for SpecTypes, [rev c1 c2] for ProgType
    (Progs => (std.map Spec (x\ y\ copy x y) SpecTypes,
    copy Prog ProgType)),
    %% Second copy: assume the clauses copying the context's eigenvariables to
    %% fresh logic variables. Then, apply the replacement to the specification
    %% types and program types obtained in the previous step, to the specification
    %% variables given as parameter to the tactic, and to the goal.
    %% Thus, following the example from the previous step, we will get
    %% [list nat] for SpecGoals, [X0] for SpecVars, [rev X0 X1] for ProgGoal
    %% If the Goal is "ordered c1", then PropGoal is "ordered X1".
    %% (note that fresh variables are present for the entire context, even if
    %% it has not been declared as specification)
    (Cs => (std.map SpecTypes (x\y\ copy x y) SpecGoals,
    std.map Spec (x\y\ copy x y) SpecVars,
    copy ProgType ProgGoal,
    copy Goal PropGoal)),
%    coq.say "Specs:" {std.map SpecGoals (t\s\ coq.term->string t s)},
%    coq.say "Spec Vars:" {std.map SpecVars (t\s\ coq.term->string t s)},
%    coq.say "Prog:" {coq.term->string ProgGoal},
%    coq.say "Prop:" {coq.term->string PropGoal},
    std.map SpecGoals (g\t\ coq.say "calling" g t, check (qgen (qheight N)) (go g t)) SpecVars,
    coq.say "Proof Term:" {std.map SpecVars (t\s\ coq.term->string t s)},
    % coq.say "Interp" {coq.term->string ProgGoal},
    interp ProgGoal,
    % coq.say "Run" {coq.term->string PropGoal},
    not (interp PropGoal),
    coq.say "Got" {coq.term->string ProgGoal}.
}}.
Elpi Typecheck.
