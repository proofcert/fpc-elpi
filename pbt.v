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
i_n : is_nat x -> insert x [] [x]
| i_s : forall y: nat, forall ys: list nat, x <= y -> insert x (y :: ys) (x :: y :: ys)
| i_c : forall y: nat, forall ys: list nat, forall rs: list nat, x > y -> insert x ys rs -> insert x (y :: ys) (x :: rs).

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
    coq.say "Spec:" SpecGoal,
    coq.say "Prog:" ProgGoal,
    coq.say "Prop:" PropGoal,
    % coq.say "0",
    check (qgen (qheight N)) (go SpecGoal),
    % coq.say "a" SpecGoal,
    interp ProgGoal,
    % coq.say "b",
    (Cs => copy Monitor Result),
    coq.say Result, 
    not (interp PropGoal),
    coq.say "Cex:" PropGoal,
    coq.say "Explain:" Cs.
}}.
Elpi Typecheck.
(* Elpi Query lp:{{not (interp {{rev [] []}})}}. *)
(* Elpi Trace. *)
Elpi Bound Steps 100000.

Goal forall x r: list nat,
is_natlist x ->
ordered_bad x -> insert 0 x r ->
ordered_bad r.

intros.
elpi pbt (H /\ H0) (H1) 15 (r0). Abort.

Goal forall x x' y: list nat,
is_natlist x -> is_natlist y -> is_natlist x' ->
append [0] x x' -> rev x y -> rev y x'.
intros.
elpi pbt (H /\ H0 /\ H1 /\ H3) (H2) 10. Abort.


Elpi Query lp:{{
  check (qgen (qheight 20)) (go {{ordered_bad [0;1;0]}}),
  interp {{insert lp:X [0;1;0] lp:Rs}},
  coq.say "List:" Rs,
  not (interp {{ordered_bad lp:Rs}}).
  }}. 

Elpi Query lp:{{
  check (qgen (qheight 30)) (go {{is_natlist lp:Xs /\ ordered_bad lp:Xs.}}),
  coq.say "List:" Xs,
  interp {{insert 0 lp:Xs lp:Rs.}},
  coq.say "Got:" Rs,
  not (interp {{ordered_bad lp:Rs.}}).
  }}. 


