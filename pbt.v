From elpi Require Import elpi.
Require Import Arith List. Import ListNotations.
Require Import Coq.Lists.List.

Inductive ordered : list nat -> Prop :=
	onl : ordered []
  | oss : forall x : nat, ordered [x]
  | ocn : forall (x y : nat) (l : list nat),
         ordered (y :: l) -> x <= y -> ordered (x :: y :: l).

(* the following is the bugged version*)
Inductive ordered_bad : list nat -> Prop :=
   onlb : ordered_bad []
  | ossb : forall x : nat, ordered_bad [x]
  | ocnb : forall (x y : nat) (l : list nat),
                ordered_bad l  -> x <= y -> ordered_bad (x:: y :: l).         

Inductive append : list nat -> list nat -> list nat -> Prop :=
   anl : forall xs, append [] xs xs
  |acn : forall xs ys zs x, 
         append xs ys zs -> append (x :: xs) ys (x :: zs).

Inductive rev : list nat -> list nat -> Prop :=
r1nl : rev [] []
| r1c : forall (x: nat) (l ts rs : list nat),
       rev l ts -> append ts [x] rs -> rev (x  :: l) rs.

(* iterative*)
Inductive revA : list nat -> list nat -> list nat -> Prop :=
rnl : forall acc, revA [] acc acc
| rc : forall (x: nat) (l acc rs : list nat),
       revA l (x :: acc) rs  -> revA (x  :: l) (x :: acc) rs.

Inductive rev2 : list nat -> list nat -> Prop :=
r: forall xs ys, revA xs [] ys -> rev2 xs ys.

Elpi Tactic pbt.
Elpi Accumulate File "pbt/src/kernel.mod".
Elpi Accumulate File "pbt/src/fpc-qbound.mod".
Elpi Accumulate lp:{{
  %% build_clauses: given a Coq context, creates copy clauses associating
  %% the eigenvariables to fresh logic variables
  type build_clauses goal-ctx -> list prop -> prop.
  build_clauses [decl Var _Name _Ty] [(copy Var X :- !)].
  build_clauses [decl Var Name Ty | Ds] [(copy Var X :- !)| Cs] :-
    build_clauses Ds Cs.
  %% env_type: given a Coq context and an eigenvariable, returns the
  %% type of that eigenvariable
  type env_type goal-ctx -> term -> term -> prop.
  env_type [decl Var _ Ty|_] Var Ty.
  env_type [decl _ _ _|L] Var Ty :- env_type L Var Ty.

  solve [trm Prog] [goal Ctx Ev Ty Who] OutGoals :-
    build_clauses Ctx Cs,
    env_type Ctx Prog ProgType,
    Cs => copy ProgType ProgGoal,
    check (qgen (qheight 4)) [] ProgGoal,
    Cs => copy Ty PropGoal,
    not (interp PropGoal),
    coq.say PropGoal.
}}.
Elpi Typecheck.
(* Elpi Query lp:{{not (interp {{rev [] []}})}}. *)

Goal forall x: list nat, ordered x -> ordered_bad x.
intros.
elpi pbt (H).
