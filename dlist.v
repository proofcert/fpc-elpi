From elpi Require Import elpi.
Require Import Arith List. Import ListNotations.
 Import Coq.Lists.List.
 Require Import dep_pbt.

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
   append ts [x] rs -> rev l ts -> rev (x  :: l) rs.

(* iterative*)
Inductive revA : list nat -> list nat -> list nat -> Prop :=
rnl : forall acc, revA [] acc acc
| rc : forall (x : nat) (l acc rs : list nat),
   revA l (x :: acc) rs  -> revA (x  :: l) acc rs.

Inductive rev2 : list nat -> list nat -> Prop :=
r: forall xs ys, revA xs [] ys -> rev2 xs ys.

Inductive insert (x:nat) : list nat -> list nat -> Prop :=
i_n : insert x [] [x]
| i_s : forall y: nat, forall ys: list nat, x <= y -> insert x (y :: ys) (x :: y :: ys)
| i_c : forall y: nat, forall ys: list nat, forall rs: list nat, x > y -> insert x ys rs -> insert x (y :: ys) (x :: rs).

(* ****** QUERIES****** *)

Goal forall xs rs, rev xs rs -> xs = rs.
intros xs rs H.
elpi dep_pbt 5 (H) (xs).
Abort.

(* false, but throws an exception*)
Goal forall x xs rs,
ordered_bad xs -> insert x xs rs -> ordered_bad rs.

intros x xs rs   H1 H2.
Fail elpi dep_pbt 3 (H1 /\ H2 ) (x) (xs). 
Abort.


(* This property is true *)
Goal forall xs rs, rev xs rs -> rev rs xs.
intros xs rs  H.
Fail elpi dep_pbt 5  (xs).
Abort.

(* This property is false *)
Goal forall xs rs, rev xs rs -> xs = rs.
intros xs rs H.
elpi dep_pbt 5 (H) (xs).
Abort.

(* true, but loops 
Goal forall xs rs, rev xs rs -> rev2 xs rs.
intros xs rs HR.
Fail elpi dep_pbt 2 (HR) (xs).
Abort.
*)
(* false, but loops 
Goal forall xs ys aps raps rxs rys,

append xs ys aps -> rev xs rxs -> rev ys rys ->
rev aps raps -> append rxs rys raps.
intros.
elpi dep_pbt 2 (H /\ H0 /\ H1 /\ H2 ) (xs) (ys).
Abort.
*)

(* OK, false *)
Goal forall x x' y: list nat,
append [0] x x' -> rev x y -> rev y x'.
intros.
elpi dep_pbt 3 (H /\ H0) (x).
Abort.