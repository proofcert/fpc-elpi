(* An example file using the kernel with dependent types and direct term construction *)
From elpi Require Import elpi.

(* The first tactic uses the kernel together with the Decide-depth 
   Proof Certificate definition, specifying a depth bound for the proof *)
Elpi Tactic dd_fpc.
Elpi Accumulate File "fpc/ljf-dep.mod".
Elpi Accumulate File "fpc/dd-fpc.mod".
Elpi Accumulate lp:{{
  solve [(int N)] [goal Ctx Ev Ty _] [] :- 
    int_to_nat N Nat,
    ljf_entry (dd Nat) Ty Ev1,
    Ev = Ev1.
    %% The kernel runs without the constraints imposed on Ev, and we only unify
    %% afterwards, so that only the complete term is checked.
}}.
Elpi Typecheck.

(* Elpi Debug "DEBUG". *)
(* Elpi Trace. *)

(* Examples using the decide depth fpc *)

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

(* The second tactic uses the Proof Certificate format of lambda terms
   in De Brujin format *)

Elpi Tactic deb_fpc.
Elpi Accumulate lp:{{
  % De Brujin-style certificates are stored here, since right now it is
  % inconvenient to pass them as parameters in the tactic invocation inside a
  % Coq proof: indeed, Elpi only supports integers, strings or Coq term as
  % arguments to tactics, and not lambda Prolog terms
  deb_certificate 1 (lambda (apply 0 [])).
  deb_certificate 2 (lambda (lambda (apply 0 []))).
  deb_certificate 3 (lambda (lambda (apply 1 [apply 0 []]))).
  deb_certificate 4 (lambda (lambda (lambda (apply 0 [apply 0 [apply 2 []]])))).
  deb_certificate 5 (lambda (lambda (apply 0 [lambda (apply 0 [apply 2 []])]))).
  deb_certificate 6 (lambda (lambda (apply 0 [lambda (apply 2 [])]))).
}}.
Elpi Accumulate File "fpc/ljf-dep.mod".
Elpi Accumulate File "fpc/deb-fpc.sig".
Elpi Accumulate File "fpc/deb-fpc.mod".
(* The tactic is built in the same way as before: we accumulate the code
   for the kernel and the fpc specification, and we provide a "solve"
   predicate that simply calls the kernel on the formula, together with
   the provided certificate. *)
Elpi Accumulate lp:{{
  solve [(int Indx)] [goal Ctx Ev Ty _] [] :- 
    deb_certificate Indx Deb,  
    Ctx => ljf_entry (lc 0 Deb) Ty Ev1,
    Ev = Ev1.
}}.
Elpi Typecheck.

Goal forall P: Prop, P -> P.
elpi deb_fpc 1.
Qed.

Goal forall P Q: Prop, Q -> (P -> P).
elpi deb_fpc 2.
Qed.

Goal forall P Q: Prop, (P -> Q) -> (P -> Q).
elpi deb_fpc 3.
Qed.

Goal forall P Q: Prop, (P -> (Q -> ((P -> P) -> P))).
elpi deb_fpc 4.
Qed.

Goal forall P Q R: Prop, (P -> ((((P -> Q) -> Q) -> R) -> R)).
elpi deb_fpc 5.
Qed.

Goal forall P Q R: Prop, (P -> ((((Q -> P) -> P) -> R) -> R)).
elpi deb_fpc 6.
Qed.
