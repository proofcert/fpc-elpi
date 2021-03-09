module dep-kernel.

type get_head term -> term -> o.
get_head (prod _ _ T) Head :- get_head (T X_) Head.
get_head (app L) (app L).

%%%%%%%%%%%%%%%
% Interpreter %
%%%%%%%%%%%%%%%

:if "DEBUG_INTERP_RAW" interp X :- coq.say X, fail.
:if "DEBUG_INTERP_RAW" backchain A B :- coq.say A B, fail.
:if "DEBUG_INTERP" interp X :- coq.say {coq.term->string X}, fail.
:if "DEBUG_INTERP" backchain A B :- coq.say {coq.term->string A} {coq.term->string B}, fail.
interp {{True}}.
interp (sort _). %:- coq.says "axiom sort".

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

:if "DEBUG_KERNEL_RAW"
check A B :- coq.say "check" A B, fail.
:if "DEBUG_KERNEL"
check Cert (bc A1 A2 Terms) :-
  coq.term->string A1 S1,
  coq.term->string A2 S2,
  std.map Terms (x\y\ coq.term->string x y) T1,
  coq.say "Backchain:" S1 "\nBC-Goal:" S2 "\nPT-List:" T1, fail.
:if "DEBUG_KERNEL"
check Cert (go A Term):-
  coq.term->string A S,
  coq.term->string Term T1,
  coq.say "Goal:" A "\nProofterm" Term, fail.

% check Cert (go X Term ):-
%   var X,
%   declare_constraint (check Cert (go X Term)) [X].

check Cert (go (sort S) Term ):-
 	tt_expert Cert,
  % coq.say "Term " {coq.term->string Term}  "has Sort" {coq.term->string (sort S)},
  coq.typecheck Term (sort S) ok. %% Resort to Coq typechecking: we could do better

check Cert (go {{lp:G1 = lp:G2}} {{eq_refl}}):-
  coq.unify-eq G1 G2 ok,
	eq_expert Cert.

check Cert (go (prod _ Ty1 Ty2) (fun _ Ty1 T)) :-
	% coq.say "calling forall right *****" ,
	pi x\ decl x _ Ty1 => check Cert (go (Ty2 x) (T x)).

check Cert (go Atom Term) :-
  coq.safe-dest-app Atom (global (indt Prog)) _Args,
  coq.env.indt Prog _ _ _ _Type Kn Clauses,
	Kons = global (indc K),
	unfold_expert Kn Cert Cert' K,
	%% Use the selected constructor as key to find its
	%% clause in the zipped list of constructors and clauses.
	std.lookup {std.zip Kn Clauses} K Clause,
	% coq.say "decide clause"  {coq.term->string Clause} "on goal" {coq.term->string Atom},
	check Cert' (bc Clause Atom ListArgs),
  coq.mk-app Kons ListArgs Term.

/*
%% WIP: Hints
check Cert (go Atom Term) :-
	% unfold_expert _ Cert Cert' _,
  hint K Type,
  get_head Type Atom,
  coq.say "Select Hint" {coq.term->string K} {coq.term->string Type},
	check Cert (bc Type Atom ListArgs),
  coq.mk-app K ListArgs Term.
*/

%% Weak head reduction
check Cert (go (app [(fun A B C)| Args]) Term) :-
  coq.mk-app (fun A B C) Args App,
  check Cert (go App Term).

%% backchain

check Cert (bc A A' []) :-
	tt_expert Cert,
  coq.unify-eq A A' ok.
  % coq.say "Init OK" {coq.term->string A}.

check Cert (bc (prod _ Ty1 (x\ Ty2)) Goal OutTerm) :-
  !,
  prod_expert Cert Cert1 Cert2,
  % coq.say "backchain IMP clause"  {coq.term->string Ty2} "on goal"{coq.term->string Goal},
  check Cert1 (bc Ty2 Goal ListArgs),
  % coq.say "go term " {coq.term->string Tm} "on goal" {coq.term->string Ty1},
  check Cert2 (go Ty1 Tm),
  OutTerm = [Tm|ListArgs].

check Cert (bc (prod _ Ty1 Ty2) Goal OutTerm) :-
  prod_expert Cert Cert1 Cert2,
  % coq.say "backchain UNIV clause"  {coq.term->string (Ty2 Tm)} "on goal"{coq.term->string Goal},
  check Cert1 (bc (Ty2 Tm) Goal ListArgs),
  % coq.say "check " {coq.term->string Tm} "on type" {coq.term->string Ty1},
  coq.typecheck Tm Ty1 ok,
%  check Cert2 (go Ty1 Tm),
  Cert2 = Cert,
  OutTerm = [Tm|ListArgs].