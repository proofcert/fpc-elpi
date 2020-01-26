From elpi Require Import elpi.
Elpi Db coq_fpc lp:{{
  solve [(int N)] [goal Ctx Ev Ty _] [] :- 
    int_to_nat N Nat,
    Ctx => ljf_entry (dd Nat) Ty Ev. 
}}.
Check ex.
Elpi Tactic coq_fpc_ng.
Elpi Accumulate File "fpc/ljf-dep.mod".
Elpi Accumulate File "fpc/dd-fpc.mod".
Elpi Accumulate Db coq_fpc.
Elpi Typecheck.

Elpi Debug "DEBUG".
(* Elpi Trace. *)
Elpi Query lp:{{ljf_entry (dd (s zero)) {{forall A: Prop, A -> A}} J.%{{fun (A:Prop) (X:A) => X}}}}.

Lemma test : forall A: Prop, A -> A.
elpi coq_fpc_ng 1.