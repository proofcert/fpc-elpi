module dep-kernel-v2.


non_atomic {{True}}.
non_atomic (sort _).
non_atomic {{lp:G1 /\ lp:G2}}.
non_atomic {{lp:G1 \/ lp:G2}}.
non_atomic {{lp:T = lp:T}}.
non_atomic {{ex (lp:G)}}.

atomic A :- not (non_atomic A).

is_imp (prod _  Ty (x\D))   Ty D.
is_uni (prod _ _Ty (x\D x)) D.

%%%%%%%%%%%%%%%
% Interpreter %
%%%%%%%%%%%%%%%

/* interp */
interp {{True}}.
interp (sort _). 
interp {{lp:G1 /\ lp:G2}} :- interp G1, interp G2.
interp {{lp:G1 \/ lp:G2}} :- interp G1; interp G2.
interp {{lp:T1 = lp:T2}} :- coq.unify-eq T1 T2 ok.
interp {{ex (lp:G)}} :- interp (G X).
interp Atom :-
  atomic Atom,
  coq.safe-dest-app Atom (global (indt Prog)) _,
  coq.env.indt Prog _ _ _ _ _ KTypes,
  std.mem KTypes D, backchain D Atom.
backchain A A' :- atomic A,  coq.unify-eq A A' ok.
backchain D A :- is_imp D A D', !, backchain D' A, interp Ty.
backchain D A :- is_uni D D',  backchain (D' X) A.
/* end */

%%%%%%%%%%%
% Checker %
%%%%%%%%%%%
/* check */
check Cert (go (sort S) A):-
  sortE Cert,
  coq.typecheck A (sort S) ok.
check Cert (go A Tm) :-
  coq.safe-dest-app A (global (indt Prog)) _,
  coq.env.indt Prog _ _ _ _ Kn KTypes,
  decideE Kn Cert Cert' K,
  std.zip Kn KTypes Clauses,
  std.lookup Clauses K D, 
  check Cert' (bc D A L),
  Tm = (app [global (indc K)|L]).
check Cert (bc (prod _ B D) A [Tm|L]) :-
  prodE Cert Cert1 Cert2 Tm,
  check Cert1 (bc (D Tm) A L),
  check Cert2 (go B Tm).
check Cert (bc A A' []) :-
  initialE Cert,
  coq.unify-eq A A' ok.
/* end */
