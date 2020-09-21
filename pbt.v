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

Inductive is_nat : nat -> Prop :=
nz: is_nat 0
| ns: forall n: nat, is_nat n -> is_nat (S n).

Inductive is_natlist : list nat -> Prop :=
nl: is_natlist []
| nlcons: forall l: list nat, forall n:nat, is_natlist l ->  is_nat n -> is_natlist (cons n l).

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

  type env_clauses goal-ctx -> list prop -> prop.
  env_clauses [decl Var _ Ty] [(copy Var Ty :- !)].
  env_clauses [decl Var _ Ty |L] [(copy Var Ty :- !)|Cs] :-
    env_clauses L Cs.

  solve [trm Prog] [goal Ctx _Ev Ty _Who] _OutGoals :-
    build_clauses Ctx Cs,
    env_clauses Ctx Progs,
    Progs => copy Prog ProgType,
    coq.say ProgType,
    Cs => copy ProgType ProgGoal,
    coq.say ProgGoal,
    check (qgen (qheight 9)) (go ProgGoal),
    coq.say "Program: " ProgGoal,
    Cs => copy Ty PropGoal,
    coq.say "Property: " PropGoal,
    not (interp PropGoal).
    % coq.say PropGoal.
}}.
Elpi Typecheck.
(* Elpi Query lp:{{not (interp {{rev [] []}})}}. *)
Elpi Trace.
Elpi Bound Steps 20.
Elpi Query lp:{{
   check (qgen (qheight 5)) (go {{is_natlist lp:X /\ ordered lp:X}}),coq.say X,fail.
}}. 


Goal forall x y: list nat, is_natlist x -> is_natlist y -> rev x y -> rev y x.
intros.
elpi pbt (H /\ H0 /\ H1).

