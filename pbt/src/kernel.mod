module kernel.

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

check Cert Ctx Type :- coq.say "check" Cert Ctx Type, fail.

check Cert [A] A.
check Cert _ (sort _) :-
	tt_expert Cert.
check Cert _ {{nat}} :-
	tt_expert Cert.
check Cert _ {{True}} :-
	tt_expert Cert.

check Cert Ctx {{lp:G1 /\ lp:G2}}:-
	and_expert Cert Cert1 Cert2,
	check Cert1 Ctx G1,
	check Cert2 Ctx G2.

check Cert Ctx {{lp:G1 \/ lp:G2}} :-
	or_expert Cert Cert' Choice,
	(
		(Choice = left, check Cert' Ctx G1)
	;
		(Choice = right, check Cert' Ctx G2)
	).

check Cert Ctx (prod _ Ty1 Ty2) :-
    prod_clerk Cert Cert',
	pi x\ check Cert' [Ty1 | Ctx] (Ty2 x).

check Cert [prod _ Ty1 Ty2] Goal :-
  prod_expert Cert Cert1 Cert2,
  check Cert1 [(Ty2 X)] Goal,
  check Cert2 [] Ty1.

check Cert [] Atom :-
    whd Atom [] (global (indt Prog)) Args, %% Coq-Elpi predicate!
    coq.env.indt Prog _ _ _ _Type Kn Clauses,
	unfold_expert Kn Cert Cert' K,
	%% Use the selected constructor as key to find its
	%% clause in the zipped list of constructors and clauses.
	std.lookup {std.zip Kn Clauses} K Clause, 
	% coq.say "Key" K "for" Atom,
	Kons = global (indc K),
	% coq.say "But OutTerm is" OutTerm,
	check Cert' [Clause] Atom.
