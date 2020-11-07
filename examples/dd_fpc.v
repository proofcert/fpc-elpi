(* Examples using the decide depth fpc *)
From elpi Require Import elpi.
Require Import coq_fpc.

Goal forall P : Prop, P -> P.
elpi dd_fpc 1.
Qed.

Goal forall P Q : Prop, P \/ P -> P.
elpi dd_fpc 1.
Qed.

Goal forall A B: Prop, A \/ B -> B \/ A.
elpi dd_fpc 2.
Qed.

Goal forall (Q: nat -> Prop), (forall x, Q x) -> Q 0.
elpi dd_fpc 1.
Qed.

Goal forall (P: Prop) (Q: Type -> Prop), (forall x, P -> Q x) -> P -> (forall x, Q x).
elpi dd_fpc 2.
Qed.

Goal forall P : nat -> Prop, (exists x, P x)  -> (exists x, P x).
elpi dd_fpc 2.
Qed.

Goal forall P Q : Type -> Prop, (exists x, (P x)) -> (forall x, (P x) -> (Q x)) -> (exists x, (Q x)).
elpi dd_fpc 3.
Qed.

Goal forall P Q, P /\ Q -> P.
  elpi dd_fpc 1.
Qed.

Goal forall P Q, P /\ Q -> Q.
  elpi dd_fpc 1.
Qed.

Goal forall P Q, P /\ Q -> Q /\ P.
  elpi dd_fpc 1.
Qed.

Goal forall P Q R, P /\ (Q /\ R) -> (P /\ Q) /\ R.
  elpi dd_fpc 1.
Qed.

Goal forall P Q : Prop, P -> P \/ Q.
  elpi dd_fpc 2.
Qed.

Goal forall A B C D : Prop, A -> (A -> B) -> (A -> B -> C) -> (A -> B -> C -> D) -> D.
elpi dd_fpc 4.
Qed.

(* Transparent biconditional. *)
Goal forall P Q : Prop, ((P -> Q) /\ (Q -> P)) -> ((Q -> P) /\ (Q -> P)).
  elpi dd_fpc 2.
Qed.

Goal forall P Q R, P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
  elpi dd_fpc 2.
Qed.

Goal forall P Q R, (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
  elpi dd_fpc 4.
Qed.

Goal forall (P Q : nat -> Prop),
    (exists x, P x) \/ (exists x, Q x) -> (exists x, P x \/ Q x).
  elpi dd_fpc 2.
Qed.

(* Transparent negation. *)
Goal forall P : Prop, False -> P.
  elpi dd_fpc 1.
Qed.

Goal forall P : Prop, (P -> False) -> (forall Q : Prop, P -> Q).
  elpi dd_fpc 2.
Qed.

Goal False -> False.
  elpi dd_fpc 1.
Qed.

Goal forall P Q : Prop, (P /\ (P -> False)) -> Q.
  elpi dd_fpc 2.
Qed.

Goal forall P : Prop, (P /\ (P -> False)) -> False.
  elpi dd_fpc 2.
Qed.

Goal forall P: Prop, P -> ((P -> False) -> False).
elpi dd_fpc 2.
Qed.

Theorem frobenius1: forall (P : Prop), forall (Q : nat -> Prop),
    (exists x, P /\ Q x) -> P /\ (exists x, Q x).
Proof. elpi dd_fpc 3. Qed.

Goal forall (P Q : nat -> Prop),
    (forall x, P x) /\ (forall x, Q x) -> (forall x, P x /\ Q x).
  elpi dd_fpc 1.
Qed.

Goal forall (P : Prop), forall (Q : nat -> Prop),
     (exists x, P \/ Q x) -> P \/ (exists x, Q x).
     elpi dd_fpc 3.
Qed.
