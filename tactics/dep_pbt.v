
(* AM: generalize to other fpc: could use more parametrization
in preprocess 

- qheight is the default (same call)
- can do qsize or pairing of height and size

    call dep_pbt size 10 
*)

From elpi Require Import elpi.

Elpi Tactic dep_pbt.
(* Debugging symbols:
RAW means no pretty printing is used for Coq terms, and
the HOAS encoding is printed.
INTERP prints calls to the prolog interpreter
KERNEL prints call to the kernel *)
(* Elpi Debug "DEBUG_INTERP". *)
(* Elpi Debug "DEBUG_INTERP_RAW". *)
(* Elpi Debug "DEBUG_KERNEL". *)
(* Elpi Debug "DEBUG_KERNEL_RAW". *)
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

  %% preprocess: combines the previous predicates.given a context and a list
  %% of arguments (intended to contain specification variables), returns
  %% three lists
  %% - The specification eigenvariables extracted from the argument
  %% - A list of copy clauses associating such eigenvariables to fresh logic variables
  %% - A list of copy clauses associating the eigenvariables to their type in the context
  %% Thus if the context has shape
  %% c1 : A
  %% c2 : (B c1)
  %% c3 : C
  %% And the supplied list of arguments is (c1) (c2), the three output list are
  %% [c1, c2]
  %% [copy c1 X0, copy c2 X1]
  %% [copy c1 A, copy c2 (B c1)]
  %          +   +     -   -     -
  type preprocess goal-ctx -> list argument -> list term -> list prop -> list prop -> prop.
  preprocess Ctx SpecT Spec  Cs Progs :-
    remove_trm SpecT Spec,
    build_clauses Ctx Cs,
    env_clauses Ctx Progs.
  
  type parse_arguments list argument -> cert -> term -> list argument -> prop.
  % default fpc: height
  parse_arguments [int N, trm Prog | SpecT] (qgen (qheight N)) Prog SpecT.
  parse_arguments [str "size", int N, trm Prog | SpecT] (qgen (qsize N M_)) Prog SpecT.
  parse_arguments [str "pair", int N, int S, trm Prog | SpecT] (pair (qgen (qheight N)) (qgen (qsize S S2_ ))) Prog SpecT.

  solve Args [goal Ctx _Ev Goal _] _OutGoals :-
    parse_arguments Args Cert Prog SpecT,
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
    std.map SpecGoals (g\t\ check Cert (go g t)) SpecVars,
    % coq.say "Proof Term:" {std.map SpecVars (t\s\ coq.term->string t s)},
    % coq.say "Interp" {coq.term->string ProgGoal},
    interp ProgGoal,
    % coq.say "Run" {coq.term->string PropGoal},
    not (interp PropGoal),
    coq.say "Counterexample:" {coq.term->string ProgGoal}.
}}.
Elpi Typecheck.
