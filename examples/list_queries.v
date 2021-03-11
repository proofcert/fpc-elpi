From elpi Require Import elpi.
Require Import Arith. 
Require Import Coq.Lists.List.
Import ListNotations.
Require Import dep_pbt.
Load list.

(* ****** DEP QUERIES****** *)

Goal forall (xs rs : list nat), rev xs rs -> xs = rs.
intros xs rs H.
elpi dep_pbt 3 (H) (xs).
elpi dep_pbt size 10 (H) (xs).
elpi dep_pbt pair 3 7 (H) (xs).
Abort.

(* same query, different type*)
Goal forall (xs rs : list bool), rev xs rs -> xs = rs.
intros xs rs H.
elpi dep_pbt 3 (H) (xs).
Abort.

Goal forall x xs rs,
ordered_bad xs -> insert x xs rs -> ordered_bad rs.
intros x xs rs   H1 H2.
elpi dep_pbt 5 (H1 /\ H2 ) (x) (xs).
Abort.

(* This property is true *)
Goal forall (xs rs : list nat), rev xs rs -> rev rs xs.
intros xs rs  H.
Fail elpi dep_pbt 2 (H) (xs).
Abort.

(* true *)
Goal forall (xs rs : list nat), rev xs rs -> rev2 xs rs.
intros xs rs HR.
Fail elpi dep_pbt 2 (HR) (xs).
Abort.

(* false *)
Goal forall (xs ys aps raps rxs rys : list nat),
append xs ys aps -> rev xs rxs -> rev ys rys ->
rev aps raps -> append rxs rys raps.
intros.
elpi dep_pbt 3 (H /\ H0 /\ H1 /\ H2 ) (xs) (ys).
Abort.

Goal forall x x' y: list nat,
append [0] x x' -> rev x y -> rev y x'.
intros.
elpi dep_pbt 3 (H /\ H0) (x).
Abort.

