(* An example tactic using the kernel with dependent types and direct term construction *)
From elpi Require Import elpi.

(* The first tactic uses the kernel together with the Decide-depth 
   Proof Certificate definition, specifying a depth bound for the proof *)
Elpi Tactic dd_fpc.
From fpc_elpi.fpc Extra Dependency "ljf-dep.mod" as ljf_dep.
From fpc_elpi.fpc Extra Dependency "dd-fpc.mod" as dd_fpc.
Elpi Accumulate File ljf_dep.
Elpi Accumulate File dd_fpc.
Elpi Accumulate lp:{{
  solve (goal _Ctx _RawEv Ty Ev [int N] as G) Out :- 
    int_to_nat N Nat,
    ljf_entry (dd Nat) Ty Ev1, coq.say "Great",
    (refine Ev1 G Out), coq.say "Yay" {coq.term->string Ev1}.
    %% The kernel runs without the constraints imposed on Ev, and we only unify
    %% afterwards, so that only the complete term is checked.
}}.
Elpi Typecheck.

(* The second tactic uses the Proof Certificate format of lambda terms
   in De Brujin format *)

Elpi Tactic deb_fpc.
Elpi Accumulate lp:{{
  % De Brujin-style certificates are stored here, since right now it is
  % inconvenient to pass them as parameters in the tactic invocation inside a
  % Coq proof: indeed, Elpi only supports integers, strings or Coq term as
  % arguments to tactics, and not lambda Prolog terms
  type deb_certificate int -> deb -> prop.
  deb_certificate 1 (lambda (apply 0 [])).
  deb_certificate 2 (lambda (lambda (apply 0 []))).
  deb_certificate 3 (lambda (lambda (apply 1 [apply 0 []]))).
  deb_certificate 4 (lambda (lambda (lambda (apply 0 [apply 0 [apply 2 []]])))).
  deb_certificate 5 (lambda (lambda (apply 0 [lambda (apply 0 [apply 2 []])]))).
  deb_certificate 6 (lambda (lambda (apply 0 [lambda (apply 2 [])]))).
  deb_certificate 7 (lambda (lambda (apply 0 [lambda (apply 2 [apply 0 []])]))).
  deb_certificate 8 (lambda (apply 0 [lambda (apply 0 [lambda (apply 2 [lambda (apply 1 [])])])])).
}}.
From fpc_elpi.fpc Extra Dependency "deb-fpc.mod" as deb_fpc.
Elpi Accumulate File ljf_dep.
Elpi Accumulate File deb_fpc.
(* The tactic is built in the same way as before: we accumulate the code
   for the kernel and the fpc specification, and we provide a "solve"
   predicate that simply calls the kernel on the formula, together with
   the provided certificate. *)
Elpi Accumulate lp:{{
  solve (goal Ctx _RawEv Ty Ev [int Indx]) [] :- 
    deb_certificate Indx Deb,  
    Ctx => ljf_entry (lc 0 Deb) Ty Ev1,
    Ev = Ev1.
}}.
Elpi Typecheck.