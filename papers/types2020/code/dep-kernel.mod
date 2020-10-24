module kernel.

%% Experimental kernel with dependent types and proof terms

get_head (prod _ _ T) Head :- get_head (T X_) Head.
get_head (app L) (app L).

flatten_app (app [X]) X.
flatten_app (global X) (global X).
flatten_app (app [X,Y | Rest]) (app [X', Y'| Rest']) :-
  flatten_app X X',
  std.map [Y|Rest] flatten_app [Y'|Rest'].

%%%%%%%%%%%%%%%
% Interpreter %
%%%%%%%%%%%%%%%

/* interp */
interp {{True}}.
interp (sort _) . 
interp {{lp:G1 /\ lp:G2}} :- !, interp G1, interp G2.
interp {{lp:G1 \/ lp:G2}} :- !, interp G1; interp G2.
interp {{lp:G = lp:G}}.
interp (app [global (indt Prog) | _Args] as Atom) :-
       coq.env.indt Prog _ _ _ _Type _Kn Clauses,
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
check Cert (go X Term ):-
  var X,
  declare_constraint (check Cert (go X Term)) [X],
check _ (go (sort S) Term ):-
  coq.typecheck Term (sort S) _. 
check Cert (go {{lp:G = lp:G}} {{eq_refl}}):-
	eq_expert Cert.
check Cert (go (prod _ Ty1 Ty2) (fun _ Ty1 T)) :-
	pi x\ decl x _ Ty1 => check Cert (go (Ty2 x) (T x)).
check Cert (go (global (indt Prog) as Atom) Term) :-
  coq.env.indt Prog _ _ _ _Type Kn Clauses,
  Kons = global (indc K),
  unfold_expert Kn Cert Cert' K,
  std.lookup {std.zip Kn Clauses} K Clause, 
  check Cert' (bc Clause Atom ListArgs),
  Term' = app [Kons | ListArgs],
  flatten_app Term' Term.
check Cert (go (app [global (indt Prog) | _Args] as  Atom) Term) :-
  coq.env.indt Prog _ _ _ _Type Kn Clauses,
	Kons = global (indc K),
	unfold_expert Kn Cert Cert' K,
	std.lookup {std.zip Kn Clauses} K Clause, 
	check Cert' (bc Clause Atom ListArgs),
	 Term' = (app [Kons|ListArgs]),
  	 flatten_app Term' Term.
check Cert (go (app [(fun A B C)| Args]) Term) :-
        coq.mk-app (fun A B C) Args App,
	 check Cert (go App Term).

check Cert (bc (prod _ Ty1 Ty2) Goal [Tm|ArgsList]) :-
        check Cert (bc (Ty2 Tm) Goal ArgsList),
  	check Cert (go Ty1 Tm).
check Cert (bc A A []) :-
	tt_expert Cert .
/* end */