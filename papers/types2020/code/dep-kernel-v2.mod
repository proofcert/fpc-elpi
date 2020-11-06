module dep-kernel-v2.

%% DM Revising the interpreter's appearance

% DM I don't see the need for this query.  If get_head succeeds, the
% work will be redone by backchain.  If get_head fails, backchain
% would succeed almost as quickly.

% get_head (prod _ _ T) Head :- get_head (T X_) Head.
% get_head (app L) (app L).

%% Support code for the interpreter put here.

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
interp {{lp:T = lp:T}}.
interp {{ex (lp:G)}} :- interp (G X).
interp Atom :- atomic Atom, definition Atom _ Clauses, 
               std.mem Clauses D, backchain D Atom.
backchain A A :- atomic A.
backchain D A :- is_imp D A D', !, backchain D' A, interp Ty.
backchain D A :- is_uni D D',  backchain (D' X) A.
/* end */

%%%%%%%%%%%
% Checker %
%%%%%%%%%%%
/* check */
check _ (go (sort S) A):- coq.typecheck A (sort S) _. 
check Cert (go A Tm) :-
  coq.safe-dest-app Atom (global (indt Prog)) _,
  coq.env.indt Prog _ _ _ _ Kn Clauses.
  unfoldE Kn Cert Cert' K,
  std.lookup {std.zip Kn Clauses} K Clause, 
  check Cert' (bc D A L),
  Tm = (app [global (indc K)|L]).
check Cert (bc (prod _ B D) G [Tm|L]) :-
  prodE Cert Cert1 Cert2,
  check Cert1 (bc (D Tm) G L),
  check Cert2 (go B Tm).
check Cert (bc A A []) :- initialE Cert.
/* end */
% check Cert (go (prod _ Ty1 Ty2) (fun _ Ty1 T)) :-
% 	pi x\ decl x _ Ty1 => check Cert (go (Ty2 x) (T x)).
