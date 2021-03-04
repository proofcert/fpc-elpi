module kernel.

%% Experimental kernel with dependent types and proof terms

get_head (prod _ _ T) Head :- get_head (T X_) Head.
get_head (app L) (app L).

/*
flatten_app (app [X]) X.
flatten_app (global X) (global X).
flatten_app (app [X,Y | Rest]) (app [X', Y'| Rest']) :-
  flatten_app X X',
  std.map [Y|Rest] flatten_app [Y'|Rest'].
*/

%%%%%%%%%%%%%%%
% Interpreter %
%%%%%%%%%%%%%%%

% interp X :- 
% %   coq.term->string X T,
%   coq.say "interp" X, fail.
% backchain A B :- 
% %   coq.term->string A T1,
% %   coq.term->string B T2,
%   coq.say "backchain" A B, fail.

interp {{True}}.
interp (sort _) . %:- coq.says "axiom sort".

interp {{lp:G1 /\ lp:G2}} :-
  !,
	interp G1,
	interp G2.

interp {{lp:G1 \/ lp:G2}} :-
  !,
	interp G1;
	interp G2.

interp {{lp:G1 = lp:G2}} :-
   !,
   coq.unify-eq G1 G2 ok.

interp (app [global (indt Prog) | _Args] as Atom) :-
%   coq.say "prog: " Prog,
%   coq.say "args: " Args,
  coq.env.indt Prog _ _ _ _Type _Kn Clauses,
	std.mem Clauses D,
	get_head D Atom,
	backchain D Atom.

backchain (prod _ Ty (x\P)) G :- !, backchain P G, interp Ty.
backchain (prod _ _Ty (x\P x)) G :- !, backchain (P X_) G.
backchain G G' :- coq.unify-eq G G' ok.

%%%%%%%%%%%
% Checker %
%%%%%%%%%%%

% check A B :- coq.say "check" A B, fail.
% check Cert (bc A1 A2 Terms) :-
%   coq.term->string A1 S1,
%   coq.term->string A2 S2,
%   std.map Terms (x\y\ coq.term->string x y) T1,
%   coq.say "check bc" S1 S2 T1, fail.
% check Cert (go A Term ):-
%   coq.term->string A S,
%   coq.term->string Term T1,
%   coq.say "check go" A Term, fail.

check Cert (go X Term ):-
  var X,
  declare_constraint (check Cert (go X Term)) [X].

check Cert (go (sort S) Term ):-
 	tt_expert Cert,
%  coq.say "Term" Term "Sort" S,
  coq.typecheck Term (sort S) _. %% Resort to Coq typechecking: we could do better
% check Cert {{nat}} :-
% 	tt_expert Cert.
% check Cert {{True}} :-
% 	tt_expert Cert.

check Cert (go {{lp:G1 = lp:G2}} {{eq_refl}}):-
  coq.unify-eq G1 G2 ok,
	eq_expert Cert.

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

check Cert (go (prod _ Ty1 Ty2) (fun _ Ty1 T)) :-
	pi x\ decl x _ Ty1 => check Cert (go (Ty2 x) (T x)).



check Cert (go Atom Term) :-
  coq.safe-dest-app Atom (global (indt Prog)) _Args,
  coq.env.indt Prog _ _ _ _Type Kn Clauses,
	Kons = global (indc K),
	unfold_expert Kn Cert Cert' K,
	%% Use the selected constructor as key to find its
	%% clause in the zipped list of constructors and clauses.
	std.lookup {std.zip Kn Clauses} K Clause, 
	check Cert' (bc Clause Atom ListArgs),
  coq.mk-app Kons ListArgs Term.

%% Perform simple reduction in the head
check Cert (go (app [(fun A B C)| Args]) Term) :-
  coq.mk-app (fun A B C) Args App,
  check Cert (go App Term).


%% backchain

% check Cert (bc (prod _ Ty1 Ty2) Goal) (fun _ (prod _ Ty1 Ty2) (x\ T (app [x, Tm]))) :-
% check Cert (bc (prod _ Ty1 Ty2) Goal (app [Tm|ArgsList])) :-


check Cert (bc A A' []) :-
	tt_expert Cert,
  coq.unify-eq A A' ok.
	
check Cert (bc (prod _ Ty1 Ty2) Goal OutTerm) :-
   prod_expert Cert Cert1 Cert2,
  check Cert1 (bc (Ty2 Tm) Goal ListArgs),
%  coq.say "backchain on" {coq.term->string Ty1} {coq.term->string (Ty2 Tm)},
  check Cert2 (go Ty1 Tm),
  OutTerm = [Tm|ListArgs].



% check Cert (go (global (indt Prog) as Atom) Kons) :-
%   coq.env.indt Prog _ _ _ _Type Kn Clauses,
%   Kons = global (indc K),
%   unfold_expert Kn Cert Cert' K,
%   %% Use the selected constructor as key to find its
%   %% clause in the zipped list of constructors and clauses.
%   std.lookup {std.zip Kn Clauses} K Clause, 
%   check Cert' (bc Clause Atom []).

% check Cert (go (global (indt Prog) as Atom) Term) :-
%   coq.env.indt Prog _ _ _ _Type Kn Clauses,
%   Kons = global (indc K),
%   unfold_expert Kn Cert Cert' K,
%   %% Use the selected constructor as key to find its
%   %% clause in the zipped list of constructors and clauses.
%   std.lookup {std.zip Kn Clauses} K Clause, 
%   check Cert' (bc Clause Atom ListArgs),
%   Term' = app [Kons | ListArgs],
%   flatten_app Term' Term.

% check Cert (go (app [global (indt Prog) | _Args] as  Atom) Kons) :-
%   coq.env.indt Prog _ _ _ _Type Kn Clauses,
% 	Kons = global (indc K),
% 	unfold_expert Kn Cert Cert' K,
% 	%% Use the selected constructor as key to find its
% 	%% clause in the zipped list of constructors and clauses.
% 	std.lookup {std.zip Kn Clauses} K Clause, 
% 	check Cert' (bc Clause Atom []).
