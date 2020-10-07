module kernel.
%% Experimental kernel with dependent types and proof terms

memb X (X :: _L).
memb X (_Y :: L) :- memb X L.

interp {{True}}.
interp {{nat}}.
interp (sort _).

interp {{lp:G1 /\ lp:G2}} :- interp G1, interp G2.
interp {{lp:G1 \/ lp:G2}} :- interp G1; interp G2.
interp {{lp:G = lp:G}}.
interp (app [global (indt Prog) | Args] as Atom) :- coq.env.indt Prog _ _ _ _Type _Kn Clauses,
	memb D Clauses,	backchain D Atom.

backchain (prod _ Ty P) G :- backchain (P X) G, interp Ty.
backchain G G.

check Cert (bc A A) (fun _ A (x\x)).
check Cert (go X) Term :- var X, declare_constraint (check Cert (go X) Term) [X],
  coq.say "Constraint su" X "(aka" {coq.term->string X}")" Term.
check _ (go (sort S)) Term :- coq.say "Term" Term "Sort" S, coq.typecheck Term (sort S) _.

check Cert (go (prod _ Ty1 Ty2)) (fun _ Ty1 T) :-
	pi x\ decl x _ Ty1 => check Cert (go (Ty2 x)) (T x).

check Cert (bc (prod _ Ty1 Ty2) Goal) (fun _ (prod _ Ty1 Ty2) (x\ T (app [x, Tm]))) :-
  check Cert (bc (Ty2 Tm) Goal) (fun _ (Ty2 Tm) T),
  coq.say "Sono il backchain su" {coq.term->string Ty1} {coq.term->string (Ty2 Tm)},
  check Cert (go Ty1) Tm.

check Cert (go (global (indt Prog) as Atom)) OutTerm :-
  coq.env.indt Prog _ _ _ _Type Kn Clauses,
  unfold_expert Kn Cert Cert' K,
  %% Use the selected constructor as key to find its
  %% clause in the zipped list of constructors and clauses.
  std.lookup {std.zip Kn Clauses} K Clause, 
  Kons = global (indc K),
  check Cert' (bc Clause Atom) (fun _ Clause Term),
  OutTerm = (Term Kons).

check Cert (go (app [global (indt Prog) | _Args] as  Atom)) OutTerm :-
    coq.env.indt Prog _ _ _ _Type Kn Clauses,
	unfold_expert Kn Cert Cert' K,
	%% Use the selected constructor as key to find its
	%% clause in the zipped list of constructors and clauses.
	std.lookup {std.zip Kn Clauses} K Clause, 
	Kons = global (indc K),
	check Cert' (bc Clause Atom) (fun _ Clause Term),
	OutTerm = (Term Kons).

%% Perform simple reduction in the head
check Cert (go (app [(fun A B C)| Args])) Term :-
  coq.mk-app (fun A B C) Args App,
  check Cert (go App) Term.
