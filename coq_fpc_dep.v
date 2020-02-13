(* An example file using the kernel with dependent types and direct term construction *)
From elpi Require Import elpi.
Elpi Db coq_fpc.db lp:{{
  solve [(int N)] [goal Ctx Ev Ty _] [] :- 
    int_to_nat N Nat,
    Ctx => ljf_entry (dd Nat) Ty Ev, coq.say "Finished" . 
}}.

Elpi Tactic coq_fpc.
Elpi Accumulate File "fpc/ljf-dep.mod".
Elpi Accumulate File "fpc/dd-fpc.mod".
Elpi Accumulate Db coq_fpc.db.
Elpi Typecheck.
 
Elpi Debug "DEBUG".
(* This query is problematic! The forall-left rule causes a problem with
   bound variables in Coq *)
Goal forall (Q: nat -> Prop), (forall x : nat, Q x) -> (forall x:nat, Q x).
Proof.
  elpi coq_fpc 2.
Qed.
(* This query is the same as the previous goal. Outside a proof, it works!
   It builds the expected term *)
(* Elpi Query lp:{{ljf_entry (dd (s (s zero))) {{forall (Q: Type -> Prop), (forall x : Type, Q x) -> (forall x:Type, Q x)}} J}}.

Elpi Debug "DEBUG".
(* Elpi Trace. *)
Elpi Query lp:{{ljf_entry (dd (s zero)) {{forall A: Prop, A -> A}} J.%{{fun (A:Prop) (X:A) => X}}}}.

Lemma test : forall A: Prop, A -> A.
elpi coq_fpc_ng 1.