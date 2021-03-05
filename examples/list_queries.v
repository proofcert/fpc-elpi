From elpi Require Import elpi.
Require Import Arith. 
Require Import Coq.Lists.List.
Import ListNotations.
Require Import pbt.
Require Import dep_pbt.
Load list.

(* ****** QUERIES****** *)

(*original query*)
Goal forall xs rs,
is_natlist xs ->
ordered_bad xs -> insert 0 xs rs ->
ordered_bad rs.
intros xs rs Gen H1 H2.
elpi pbt (Gen /\ H1) (H2) 5 (rs). (* why rs?*) 

elpi pbt (Gen /\ H1) (H2) 5 (xs /\ rs).
Abort.

(* with generation only of natlist*)

Goal forall xs rs,
is_natlist xs -> ordered_bad xs -> insert 0 xs rs -> ordered_bad rs.
intros xs rs Gen H1 H2.
elpi pbt (Gen) (H1 /\ H2) 5 (rs). 
Abort.

(* generating both nat and natlist*)

Goal forall x xs rs,

is_nat x -> is_natlist xs -> ordered_bad xs -> insert x xs rs -> ordered_bad rs.

intros x xs rs GenN GenL  H1 H2.
elpi pbt (GenN /\ GenL ) (H1 /\ H2) 5 (rs). 
Abort.

(* This property is true *)
Goal forall xs rs, is_natlist xs -> rev xs rs -> rev rs xs.
intros xs rs Gen H.
Fail elpi pbt (Gen) (H) 5 (xs).
Abort.

(* This property is false *)
Goal forall xs rs, is_natlist xs -> rev xs rs -> xs = rs.
intros xs rs Gen H.
elpi pbt (Gen) (H) 4 (rs).
Abort.

(* true *)
Goal forall xs rs, is_natlist xs -> rev xs rs -> rev2 xs rs.
intros xs rs Gen HR.
Fail elpi pbt (Gen) (HR) 5 (xs).
Abort.

(* false *)
Goal forall xs ys aps raps rxs rys,
is_natlist xs -> is_natlist ys -> 
append xs ys aps -> rev xs rxs -> rev ys rys ->
rev aps raps -> append rxs rys raps.
intros.
elpi pbt (H /\ H0) (H1 /\ H2 /\ H3 /\ H4) 4 (xs /\ ys).
Abort.

Goal forall x x' y: list nat,
is_natlist x -> 
append [0] x x' -> rev x y -> rev y x'.
intros.
elpi pbt (H) (H0 /\ H1) 5 (x).
Abort.


(* ****** DEP QUERIES****** *)

Goal forall (xs rs : list nat), rev xs rs -> xs = rs.
intros xs rs H.
elpi dep_pbt 3 (H) (xs).
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
Fail elpi dep_pbt 5 (H) (xs).
Abort.

(* true *)
Goal forall (xs rs : list nat), rev xs rs -> rev2 xs rs.
intros xs rs HR.
Fail elpi dep_pbt 5 (HR) (xs).
Abort.

(* false *)
Goal forall (xs ys aps raps rxs rys : list nat),
append xs ys aps -> rev xs rxs -> rev ys rys ->
rev aps raps -> append rxs rys raps.
intros.
elpi dep_pbt 5 (H /\ H0 /\ H1 /\ H2 ) (xs) (ys).
Abort.

Goal forall x x' y: list nat,
append [0] x x' -> rev x y -> rev y x'.
intros.
elpi dep_pbt 3 (H /\ H0) (x).
Abort.

Goal forall x y: list nat,
rev (app [2] x) y.

intros.
elpi dep_pbt 3 (True) (x).