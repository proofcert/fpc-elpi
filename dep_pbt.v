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

Inductive insert (x:nat) : list nat -> list nat -> Prop :=
i_n : insert x [] [x]
| i_s : forall y: nat, forall ys: list nat, x <= y -> insert x (y :: ys) (x :: y :: ys)
| i_c : forall y: nat, forall ys: list nat, forall rs: list nat, x > y -> insert x ys rs -> insert x (y :: ys) (x :: rs).

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
    std.map SpecGoals (g\t\ check (qgen (qheight N)) (go g t)) SpecVars,
    coq.say "Proof Term:" {std.map SpecVars (t\s\ coq.term->string t s)},
    coq.say "Interp" {coq.term->string ProgGoal},
    interp ProgGoal,
    coq.say "Got" {coq.term->string ProgGoal},
    not (interp PropGoal),
    coq.say "Cex:" PropGoal.
}}.
Elpi Typecheck.
(* Elpi Trace.  *)
Elpi Debug "DEBUG_CHECK".

Goal forall x r : list nat, forall n: nat,
(* is_natlist x -> is_nat n -> *)
ordered_bad x -> insert n x r ->
ordered_bad r.

intros.
elpi dpbt (H) (H0) 5 (x).
Abort.

Elpi Query lp:{{
  check (qgen (qheight 5)) (go {{exists n:nat, exists p:is_nat n, True}}) T.
}}.

Goal forall x x' y: list nat,
is_natlist x -> is_natlist y -> is_natlist x' ->
append [0] x x' -> rev x y -> rev y x'.
intros.
elpi pbt (H /\ H0 /\ H1 /\ H3) (H2) 10 (x). Abort.
