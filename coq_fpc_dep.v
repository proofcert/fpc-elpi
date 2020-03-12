(* An example file using the kernel with dependent types and direct term construction *)

From elpi Require Import elpi.
Elpi Db coq_fpc.db lp:{{
  solve [(int N)] [goal Ctx Ev Ty _] [] :- 
    int_to_nat N Nat,
    Ctx => ljf_entry (dd Nat) Ty Ev1,
           Ev = Ev1.
           %% The kernel runs without the constraints imposed on Ev, and we only unify
           %% afterwards, so that only the complete term is checked.
}}.
Elpi Tactic coq_fpc.
Elpi Accumulate File "fpc/ljf-dep.mod".
Elpi Accumulate File "fpc/dd-fpc.mod".
Elpi Accumulate Db coq_fpc.db.
Elpi Typecheck.
Elpi Debug "DEBUG".
(* Elpi Trace. *)

Goal forall P : Prop, P -> P.
elpi coq_fpc 1.
Qed.

Goal forall P Q : Prop, P \/ P -> P.
elpi coq_fpc 1.
Qed.

Goal forall A B: Prop, A \/ B -> B \/ A.
elpi coq_fpc 2.
Qed.

Goal forall (Q: nat -> Prop), (forall x, Q x) -> Q 0.
elpi coq_fpc 1.
Qed.

Goal forall (P: Prop) (Q: Type -> Prop), (forall x, P -> Q x) -> P -> (forall x, Q x).
elpi coq_fpc 2.
Qed.

Goal forall P : nat -> Prop, (exists x, P x)  -> (exists x, P x).
elpi coq_fpc 2.
Qed.

Goal forall P Q : Type -> Prop, (exists x, (P x)) -> (forall x, (P x) -> (Q x)) -> (exists x, (Q x)).
elpi coq_fpc 3.
Qed.