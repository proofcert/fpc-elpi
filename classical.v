(* Some experiments with a classical hosted kernel *)
From elpi Require Import elpi.

Elpi Tactic classical_dd_fpc.
Elpi Accumulate File "fpc/ljf-dep.mod".
Elpi Accumulate File "fpc/classical/lkf-hosted.mod".
Elpi Accumulate File "fpc/classical/dd_classical-fpc.mod".
Elpi Accumulate lp:{{
%   solve [(int N)] [goal Ctx Ev Ty _] [] :- 
  solve [(int N)] [goal Ctx Ev Ty _] [] :- 
    lkf_entry (dd N) Ty Ev1,
    Ev = Ev1.
    %% The kernel runs without the constraints imposed on Ev, and we only unify
    %% afterwards, so that only the complete term is checked.
}}.
Elpi Typecheck.

Elpi Query lp:{{
  lkf_entry (dd 1) {{forall P:Prop, (P -> False)}} F.
}}.

Elpi Query lp:{{
  lkf_entry (dd 1) {{forall P:Prop, P \/ (P -> False)}} Term.
}}.

