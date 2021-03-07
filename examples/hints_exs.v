From Coq Require Import Lia.

Print O.
(* 
Commutativity of add.

Two lemmas and a theorem where auto uses that theorem. 
There are inductive proofs and auto/dprolog would be used to 
complete the proof. We use new hints db to simulate elpi db*)


Inductive add: nat -> nat -> nat -> Prop :=
|ad0 x: add O x x
| ads x y z : add x y z -> add (S x) y (S z).

(* This comes from free in dprolog*)
Create HintDb add_core.
Hint Constructors add : add_core.
Print HintDb add_core.

Theorem add_base: forall x, add x 0 x.
intro x. induction x; auto with add_core. 
Qed.
Hint Resolve add_base : add_core.
Theorem add_step : forall A B C, add A B C -> add A (S B) (S C). 
Proof.
induction  1; auto with add_core. 
Qed.
Hint Resolve add_step : add_core.

Theorem add_comm : forall A B C, add A B C -> add B A C.
induction  1;  auto with add_core. 
Qed.



(* path example *)


Section path.

Parameter node : Set.
Parameter edge : node -> node -> Prop.

Inductive path : node -> node -> Prop:=
  | nr x: path x x 
  | nt x y z : edge x z -> path z y -> path x y.
Print path.

Lemma ptrans: forall x y z, path x z -> path z y -> path x y.
Proof.
intros x y z Hx Hz.
(* generalize dependent z. *)
induction Hx; eauto using nt.
Qed.
End path.
Print ptrans.
(* A bunch of examples we cannot emulate because "not Horn"*)
Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Proof.
intros.
apply H2.
- apply H3. intros. apply H. assumption. assumption.
- assumption. 
Restart.
info_auto with nocore. Qed.
Print auto_example_2.


Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. lia. Qed.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
intros.
apply le_antisym.
apply H. apply H0.
Restart.
info_auto using le_antisym.
Qed.
Print auto_example_6.
  
  Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof. info_auto. Qed.

