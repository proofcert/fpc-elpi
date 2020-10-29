module kernel.

%% Experimental kernel with dependent types and proof terms

get_head (prod _ _ T) Head :- get_head (T X_) Head.
get_head (app L) (app L).

%%%%%%%%%%%%%%%
% Interpreter %
%%%%%%%%%%%%%%%

/* interp */
interp {{True}}.
interp (sort _) . 
interp {{lp:G1 /\ lp:G2}} :- !, interp G1, interp G2.
interp {{lp:G1 \/ lp:G2}} :- !, interp G1; interp G2.
interp {{lp: T = lp:T}} :- !.
interp{{ex (lp:G)}} :- !, interp (G X).
interp (app [global (indt Prog) | _] as Atom) :-
  coq.env.indt Prog _ _ _ _  _ Clauses,
  std.mem Clauses D,
  get_head D Atom,
  backchain D Atom.
backchain (prod _ Ty (x\P)) A :- !, backchain P A, interp Ty.
backchain (prod _ _Ty (x\P x)) A :- !, backchain (P X) A.
backchain A A.
/* end */

%%%%%%%%%%%
% Checker %
%%%%%%%%%%%
/* check */
check _ (go (sort S) Term ):-
  coq.typecheck Term (sort S) _. 
check Cert (go (prod _ Ty1 Ty2) (fun _ Ty1 T)) :-
	pi x\ decl x _ Ty1 => check Cert (go (Ty2 x) (T x)).
check Cert (go Atom Term) :-
  coq.safe-dest-app Atom (global (indt Prog)) _Args,
  coq.env.indt Prog _ _ _ _Type Kn Clauses,
	Kons = global (indc K),
	unfold_expert Kn Cert Cert' K,
	std.lookup {std.zip Kn Clauses} K Clause, 
	check Cert' (bc Clause Atom ListArgs),
        Term = (app [Kons|ListArgs]).
check Cert (go (app [(fun A B C)| Args]) Term) :-
        coq.mk-app (fun A B C) Args App,
	 check Cert (go App Term).
check Cert (bc (prod _ Ty1 Ty2) Goal [Tm|ArgsList]) :-
        prod_expert Cert Cert1 Cert2,
        check Cert1 (bc (Ty2 Tm) Goal ArgsList),
  	check Cert2 (go Ty1 Tm).
check Cert (bc A A []) :-
	tt_expert Cert .
/* end */