(* Check ex.
Check or_ind. *)
(* An example file using the kernel with dependent types and direct term construction *)
From elpi Require Import elpi.
Elpi Db coq_fpc.db lp:{{
  solve [(int N)] [goal Ctx Ev Ty _] [] :- 
    int_to_nat N Nat,
    Ctx => ljf_entry (dd Nat) Ty Ev1, Ev = Ev1. %% It looks like the unification forces some sort of normalization
                                                %% This is needed for the tactic to work
}}.
Elpi Tactic coq_fpc.
Elpi Accumulate File "fpc/ljf-dep.mod".
Elpi Accumulate File "fpc/dd-fpc.mod".
Elpi Accumulate Db coq_fpc.db.
Elpi Typecheck.
 
Elpi Debug "DEBUG".

Elpi Query lp:{{ljf_entry (dd (s (s (s zero)))) {{forall P : nat -> Prop, (exists x, P x)  -> (exists x, P x)}} Term.}}.
Goal forall P : nat -> Prop, (exists x, P x)  -> (exists x, P x).
elpi coq_fpc 2.
Qed.
Elpi Query lp:{{coq.typecheck {{(fun (P : nat -> Prop) (H : exists x : nat, P x) => H) }} Ty.}}.
Elpi Query lp:{{ljf_entry (dd (s (s (s zero)))) {{forall P : nat -> Prop, (exists x, P x)  -> (exists x, P x)}} {{(fun (P : nat -> Prop) (H : exists x : nat, P x) => H)}}.}}.
Goal forall P : nat -> Prop, (exists x, P x)  -> (exists x, P x).
elpi coq_fpc 3.
Goal forall P Q : Type -> Prop, forall x, forall y, ((P x) -> (Q y)) -> (exists x, (P x) -> forall y, (Q y)).
elpi coq_fpc 2.
Elpi Query lp:{{ljf_entry (dd (s (s zero))) {{forall (Q: nat -> Prop), (forall x : nat, Q x) -> (forall x:nat, Q x)}} J}}.
Goal forall (Q: nat -> Prop), (forall x : nat, Q x) -> (forall x:nat, Q x).
Proof.
  elpi coq_fpc 2.
Qed.
(* This query is the same as the previous goal. Outside a proof, it works!
   It builds the expected term *)
(* Elpi Query lp:{{ljf_entry (dd (s (s zero))) {{forall (Q: Type -> Prop), (forall x : Type, Q x) -> (forall x:Type, Q x)}} J}}.

(* Elpi Trace. *)
Elpi Query lp:{{ljf_entry (dd (s (s (s zero))))  {{forall (P: Prop) (Q: Type -> Prop), (forall x, P -> Q x) -> P -> (forall x, Q x)}}
X}}.
Elpi Query lp:{{ljf_entry (dd  (s (s zero))) {{forall P:Prop, (P->P)}} X}}.
Elpi Query lp:{{ljf_entry (dd  (s (s zero))) {{forall P Q:Prop, (P->Q) -> P -> Q}} X}}.
Goal forall P Q:Prop, (P->Q) -> P -> Q.
elpi coq_fpc 2.
Qed.

*)
Elpi Query lp:{{ljf_entry (dd (s zero)) {{forall P: Prop, P \/ P -> P}} X}}.

Goal forall P : Prop, P -> P.
elpi coq_fpc 1.
Qed.

(* Goal forall P Q : Prop, P \/ P -> P.
elpi coq_fpc 1.
Qed. *)
Goal forall (Q: Prop), Q -> (forall x:nat, Q).
Proof.
  elpi coq_fpc 2.
  Show Proof.
Qed.
Goal forall (Q: nat -> Prop), (forall x, Q x) -> Q 0.
Proof.
elpi coq_fpc 1.
Qed.
Goal forall (P: Prop) (Q: Type -> Prop), (forall x, P -> Q x) -> P -> (forall x, Q x).
Proof.
  elpi coq_fpc 2.
Qed.

Goal forall A: Prop, A -> A.
elpi coq_fpc 1.
Qed.

Goal forall A B: Prop, A \/ B -> B \/ A.
elpi coq_fpc 1.
Qed.