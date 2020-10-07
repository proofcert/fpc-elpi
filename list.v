From elpi Require Import elpi.
Require Import Arith List. Import ListNotations.
 Import Coq.Lists.List.
 Require Import pbt.

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

(* ****** QUERIES****** *)


(*original query*)
Goal forall xs rs,
is_natlist xs ->
ordered_bad xs -> insert 0 xs rs ->
ordered_bad rs.

intros xs rs Gen H1 H2.
elpi pbt (Gen /\ H1) (H2) 15 (rs). 
Abort.


(* with generation only of natlist*)

Goal forall xs rs,
is_natlist xs -> ordered_bad xs -> insert 0 xs rs -> ordered_bad rs.

intros xs rs Gen H1 H2.
elpi pbt (Gen) (H1 /\ H2) 15 (rs). 
Abort.

(* generating both nat and natlist*)

Goal forall x xs rs,
is_nat x -> is_natlist xs -> ordered_bad xs -> insert x xs rs -> ordered_bad rs.

intros x xs rs GenN GenL  H1 H2.
elpi pbt (GenN /\ GenL ) (H1 /\ H2) 15 (rs). 
Abort.


(* This property is true*)
Goal forall xs rs, is_natlist xs -> rev xs rs -> rev rs xs.
intros xs rs Gen H.
Fail elpi pbt Gen H 10.
Abort.

(* This property is false and still solve does not handle it*)
Goal forall xs rs, is_natlist xs -> rev xs rs -> xs = rs.
intros xs rs Gen H.
Fail elpi pbt Gen H 15 (xs).
Abort.

(* true *)
Goal forall xs rs, is_natlist xs -> rev xs rs -> rev2 xs rs.
intros xs rs Gen HR.
Fail elpi pbt Gen HR 15.
Abort.

(* false but it fails to find cex*)
Elpi Bound Steps 10000.

Goal forall xs ys aps raps rxs rys,
is_natlist xs -> is_natlist ys -> 
append xs ys aps -> rev xs rxs -> rev ys rys ->
rev aps raps -> append rxs rys raps.
intros.
Fail elpi pbt (H /\ H0) (H1 /\ H2 /\ H3 /\ H4) 3 (xs /\ ys).
Abort.
Goal forall x x' y: list nat,
is_natlist x -> is_natlist x' ->
append [0] x x' -> rev x y -> rev y x'.

intros.
Fail elpi pbt (H /\ H0) (H1 /\ H2) 5 (x).
Abort.

(*
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


*)