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
    coq_say "MARIA IO ESCO" Ev1,
    Ev = Ev1.
    %% The kernel runs without the constraints imposed on Ev, and we only unify
    %% afterwards, so that only the complete term is checked.
}}.
Elpi Typecheck.
(* Elpi Tactic veryclever.
Elpi Accumulate lp:{{
  solve _ [goal _ Ev _ _] [] :-
  Ev = fun `P` (sort prop) c0 \
 fun `Q` (prod `_` (global (indt «nat»)) c1 \ sort prop) c1 \
  fun _ 
   (app
	 [global (indt «ex»), X1 c0 c1, 
      (fun `x` _ c2 \ app [global (indt «or»), c0, app [c1, c2]])]) 
   c2 \
   app
    [global (const «ex_ind»), X61 c0 c1, X62 c0 c1, X63 c0 c1, 
     (fun (X64 c0 c1) (X1 c0 c1) c3 \
       fun (X65 c0 c1) (app [global (indt «or»), c0, app [c1, c3]]) c4 \
        app
         [global (const «or_ind»), c0, app [c1, c3], 
          app
           [global (indt «or»), c0, 
            app
             [global (indt «ex»), X8 c0 c1, 
              (fun `x` (X8 c0 c1) c5 \ app [c1, c5])]], 
          (fun (X66 c0 c1 c3) c0 c5 \
            app
             [global (indc «or_introl»), X67 c0 c1 c3 c5, X68 c0 c1 c3 c5, 
              c5]), 
          (fun (X69 c0 c1 c3) (app [c1, c3]) c5 \
            app
             [global (indc «or_intror»), X70 c0 c1 c3 c5, X71 c0 c1 c3 c5, 
              app
               [global (indc «ex_intro»), X8 c0 c1, 
                (fun (X72 c0 c1 c3 c5) (X8 c0 c1) c6 \ app [c1, c6]), c3, c5]]), 
          c4]), c2]
}}. *)

Goal forall (P : Prop), forall (Q : nat -> Prop),
     (exists x, P \/ Q x) -> P \/ (exists x, Q x).
     apply (
       fun P => fun Q => fun H =>
       ex_ind
       (fun x => fun y =>
       (or_ind (fun or1 => or_introl or1)
               (fun or2 => or_intror (ex_intro (fun c6 => Q c6) x or2)) y)) H).
Elpi Query lp:{{
  ljf_entry (dd (s (s (s zero)))) {{forall (P : Prop), forall (Q : nat -> Prop), (exists x, P \/ Q x) -> P \/ (exists x, Q x)}}
  {{
       fun P => fun Q => fun H =>
       ex_ind
       (fun x => fun y =>
       (or_ind (fun or1 => or_introl or1)
               (fun or2 => or_intror (ex_intro (fun c6 => Q c6) x or2)) y)) H}}.
}}.
Elpi Query lp:{{
  coq.say
  {{
       fun P => fun Q => fun H =>
       ex_ind
       (fun x => fun y =>
       (or_ind (fun or1 => or_introl or1)
               (fun or2 => or_intror (ex_intro (fun c6 => Q c6) x or2)) y)) H}}.
}}.
Goal forall (P : Prop), forall (Q : nat -> Prop),
     (exists x, P \/ Q x) -> P \/ (exists x, Q x).
     elpi dd_fpc 3.
     intros.
     (* firstorder. *)
     Show Proof.
     apply (
       ex_ind
       (fun x => fun y =>
       (or_ind (fun or1 => or_introl or1)
               (fun or2 => or_intror (ex_intro (fun c6 => Q c6) x or2)) y)) H).
     
  elpi dd_fpc 3.
Check or_introl.
Elpi Debug "DEBUG".
(* Elpi Trace. *)

Elpi Tactic veryclever.
Elpi Accumulate lp:{{
  solve _ [goal _ Ev _ _] [] :-
  Ev = fun _ (sort prop) c0 \
 fun _ (sort prop) c1 \
  fun _ (sort prop) c2 \
   fun _ (sort prop) c3 \
	fun _ c0 c4 \
     fun _ (prod `_` c0 c5 \ c1) c5 \
      fun _ (prod `_` c0 c6 \ prod `_` c1 c7 \ c2) 
       c6 \
       fun _ 
        (prod `_` c0 c7 \ prod `_` c1 c8 \ prod `_` c2 c9 \ c3) c7 \
        app
         [app [app [c7, c4], app [c5, c4]], app [app [c6, c4], app [c5, c4]].
}}.
Elpi Typecheck.
Theorem chaining : forall A B C : Prop, A -> (A -> B) -> (A -> B -> C) -> C.
elpi dd_fpc 4.
Show Proof.
Qed.
Elpi Query lp:{{
  ljf_entry (dd (s (s (s (s zero))))) {{forall A B C D: Prop, A -> (A -> B) -> (A -> B -> C) -> (A -> B -> C -> D) -> D}}
  X.
}}.

Theorem chaining : forall A B C D : Prop, A -> (A -> B) -> (A -> B -> C) -> (A -> B -> C -> D) -> D.
elpi dd_fpc 6.
Qed.

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
  deb_certificate 7 (lambda (lambda (apply 0 [lambda (apply 2 [apply 0 []])]))).
  deb_certificate 8 (lambda (apply 0 [lambda (apply 0 [lambda (apply 2 [lambda (apply 1 [])])])])).
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

Theorem dneg_exc_mid : forall P Q : Prop, ((P -> Q) -> ((P -> Q) -> Q) -> Q).
Proof. elpi deb_fpc 7. Qed.

Theorem dneg_peirce_mid : forall P Q: Prop, (((((P -> Q) -> P) -> P) -> Q) -> Q).
Proof. elpi deb_fpc 8. Qed.
