module kernel.

%% Experimental kernel with dependent types and proof terms

%%%%%%%%%%%%%%%%%%%%%
% Helper predicates %
%%%%%%%%%%%%%%%%%%%%%

memb X (X :: _L).
memb X (_Y :: L) :- memb X L.

%%%%%%%%%%%%%%%
% Interpreter %
%%%%%%%%%%%%%%%

% interp X :- coq.say "interp" X, fail.
interp {{True}}.
interp {{nat}}. % :- coq.says "axiom nat", true.
interp (sort _) . %:- coq.says "axiom sort".

interp {{lp:G1 /\ lp:G2}} :-
	interp G1,
	interp G2.

interp {{lp:G1 \/ lp:G2}} :-
	interp G1;
	interp G2.

% interp (some G) :-
% 	interp (G _).

% interp (nabla G) :-
% 	pi x\ interp (G x).

interp {{lp:G = lp:G}}.


interp (app [global (indt Prog) | Args] as Atom) :-
%   coq.say "prog: " Prog,
%   coq.say "args: " Args,
    coq.env.indt Prog _ _ _ _Type _Kn Clauses,
	memb D Clauses,
	%  coq.say "selected: " D,
	backchain D Atom.

% commented -AM
% interp G :- cl C Var, backchain C G.

% trace changed  -AM
% backchain A B :- coq.say "backchain with clause: " A, fail.
backchain (prod _ Ty P) G :- backchain (P X) G, interp Ty.
backchain G G.

%%%%%%%%%%%
% Checker %
%%%%%%%%%%%

check Cert (bc A1 A2) Term :-
  coq.term->string A1 S1,
  coq.term->string A2 S2,
  coq.term->string Term T1,
  coq.say "check bc" A1 A2 T1, fail.
check Cert (go A) Term :-
  coq.term->string A S,
  coq.term->string Term T1,
  coq.say "check go" A T1, fail.

check Cert (bc A A) (fun _ A (x\x)).
check Cert (go X) Term :-
  var X,
  declare_constraint (check Cert (go X) Term) [X],
  coq.say "Constraint su" X "(aka" {coq.term->string X}")" Term.
check _ (go (sort S)) Term :-
  coq.say "Term" Term "Sort" S,
  coq.typecheck Term (sort S) _.
%   coq.say "Type" Type,
%   coq.typecheck Term (sort S) _. %% Resort to Coq typechecking: we could do better
% check Cert (sort _) :-
% 	tt_expert Cert.
% check Cert {{nat}} :-
% 	tt_expert Cert.
% check Cert {{True}} :-
% 	tt_expert Cert.

% check Cert {{lp:G = lp:G}} :-
% 	eq_expert Cert.

% check Cert (go {{lp:G1 /\ lp:G2}}) {{conj lp:T1 lp:T2}}:-
% 	and_expert Cert Cert1 Cert2,
% 	check Cert1 (go G1) T1,
% 	check Cert2 (go G2) T2.

% check Cert (go {{lp:G1 \/ lp:G2}}) Term :-
% 	or_expert Cert Cert' Choice,
% 	(
% 		(Choice = left, Term = {{or_introl lp:T}}, check Cert' (go G1) T)
% 	;
% 		(Choice = right, Term = {{or_intror lp:T}}, check Cert' (go G2) T)
% 	).

% check Cert (some G) :-
% 	some_expert Cert Cert' T,
% 	check Cert' (G T).

% check Cert (nabla G) :-
% 	pi x\ check Cert (G x).
check Cert (go (prod _ Ty1 Ty2)) (fun _ Ty1 T) :-
  coq.say "CIao",
	pi x\ decl x _ Ty1 => check Cert (go (Ty2 x)) (T x).

check Cert (bc (prod _ Ty1 Ty2) Goal) (fun _ (prod _ Ty1 Ty2) (x\ T (app [x, Tm]))) :-
  check Cert (bc (Ty2 Tm) Goal) (fun _ (Ty2 Tm) T),
  coq.say "Sono il backchain su" {coq.term->string Ty1} {coq.term->string (Ty2 Tm)},
  check Cert (go Ty1) Tm.
  %% Suggestion from a call: beta T Tm Term ???

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
