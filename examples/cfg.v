(*CGF example from Aho & Ulhmann p 81 and its mutations
as described in Nitpick's manual p 28
S := . | bA | aB
A := aS | bAA
B := bS | aBB

Property: word W is in S iff it contains equal numbers of a and b

would be nicer to allow some computations inside the Inductive
and in the property
*)


From elpi Require Import elpi.
Require Import Arith List. Import ListNotations.
Require Import Coq.Lists.List.
Require Import pbt.
Require Import dep_pbt.

Inductive append  {A : Set} :list A -> list A -> list A -> Prop :=
anl : forall xs, append [] xs xs
|acn : forall xs ys zs x, 
     append xs ys zs -> append (x :: xs) ys (x :: zs).


Inductive alphabet := a | b.
Inductive ss : list alphabet -> Prop :=
| sn : ss []
| sb w : aa w -> ss (b :: w)
| sa w : bb w -> ss (a :: w)

with aa   : list alphabet -> Prop :=

|aas w: ss w -> aa (a ::w)  
|aab v w vw : aa v -> aa w -> append v w vw -> aa (b :: vw)

with bb   : list alphabet -> Prop :=
|bbs w: ss w -> bb (b ::w)  
|bba v w vw : bb v -> bb w -> append v w vw -> bb (a :: vw)
.


Inductive count : alphabet -> list alphabet -> nat -> Prop :=
       | c1 X:  count X [] O
       | c2 X XS N: count X XS N -> count X (cons X XS) ( N + 1)
       | c3 X Y XS N:  X <> Y -> count X XS N -> count X (cons Y XS) N .

Definition sounds (SS : list alphabet -> Prop): Prop :=
    forall W N1 N2, ( SS W -> count a W N1 -> count b W N2 -> N1 = N2).

 (* similar properties for aa bb
 
 
Define soundA : prop by
        soundA := forall W N, word W -> aa W -> count a W N -> count b W (s N).

Define soundB : prop by
        soundB := forall W N, word W -> bb W -> count a W (s N) -> count b W N.
 *)   

 Goal sounds ss.
 unfold sounds.
 intros.
 Fail  elpi pbt (H) (H0 /\ H1) 10 (W).
 Abort.

 Module G1.
Inductive ss : list alphabet -> Prop :=
| sn : ss []
| sb w : ss w -> ss (b :: w) (*bug ss w should be aa w*)
| sa w : bb w -> ss (a :: w)

with aa   : list alphabet -> Prop :=

|aas w: ss w -> aa (a ::w)  
|aab v w vw : aa v -> aa w -> append v w vw -> aa (b :: vw)

with bb   : list alphabet -> Prop :=
|bbs w: ss w -> bb (b ::w)  
|bba v w vw : bb v -> bb w -> append v w vw -> bb (a :: vw)
.
 End G1.

 Goal sounds G1.ss.
 unfold sounds.
 intros.
  Fail elpi pbt (H) (H0 /\ H1) 10 (W).
 Abort.