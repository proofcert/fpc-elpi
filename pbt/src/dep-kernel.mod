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

% check Cert Ctx Type Term :- coq.say "check" Cert Ctx Type Term, fail.

check Cert [A] A (fun _ A (x\x)).
check _ [] (sort S) Term :-
  coq.typecheck Term (sort S) _. %% Resort to Coq typechecking: we could do better
% check Cert (sort _) :-
% 	tt_expert Cert.
% check Cert {{nat}} :-
% 	tt_expert Cert.
% check Cert {{True}} :-
% 	tt_expert Cert.

% check Cert {{lp:G = lp:G}} :-
% 	eq_expert Cert.

check Cert Ctx {{lp:G1 /\ lp:G2}} {{conj lp:T1 lp:T2}}:-
	and_expert Cert Cert1 Cert2,
	check Cert1 Ctx G1 T1,
	check Cert2 Ctx G2 T2.

check Cert Ctx {{lp:G1 \/ lp:G2}} Term :-
	or_expert Cert Cert' Choice,
	(
		(Choice = left, Term = {{or_introl lp:T}}, check Cert' Ctx G1 T)
	;
		(Choice = right, Term = {{or_intror lp:T}}, check Cert' Ctx G2 T)
	).

% check Cert (some G) :-
% 	some_expert Cert Cert' T,
% 	check Cert' (G T).

% check Cert (nabla G) :-
% 	pi x\ check Cert (G x).

check Cert Ctx (prod _ Ty1 Ty2) (fun _ Ty1 T) :-
	pi x\ check Cert [Ty1 | Ctx] (Ty2 x) (T x).

check Cert [prod _ Ty1 Ty2] Goal (fun _ (prod _ Ty1 Ty2) (x\ T (app [x, Tm]))) :-
  check Cert [(Ty2 Tm)] Goal (fun _ (Ty2 Tm) T),
  check Cert [] Ty1 Tm.

check Cert [] Atom OutTerm :-
    whd Atom [] (global (indt Prog)) Args, %% Coq-Elpi predicate!
    coq.env.indt Prog _ _ _ _Type Kn Clauses,
	unfold_expert Kn Cert Cert' K,
	%% Use the selected constructor as key to find its
	%% clause in the zipped list of constructors and clauses.
	std.lookup {std.zip Kn Clauses} K Clause, 
	% coq.say "Key" K "for" Atom,
	Kons = global (indc K),
	% coq.say "But OutTerm is" OutTerm,
	check Cert' [Clause] Atom (fun _ Clause Term),
	% coq.say "Ok" K "with" Term,
	OutTerm = (Term Kons).

%% This would do without lProlog-HOAS substitutions, and uses
%% instead pure Coq applications. Does not work at the moment

% check Cert [] Atom {{lp:Kons}} :-
%     whd Atom [] (global (indt Prog)) Args, %% Coq-Elpi predicate!
%     coq.env.indt Prog _ _ _ _Type Kn Clauses,
% 	unfold_expert Kn Cert Cert' K,
% 	std.lookup {std.zip Kn Clauses} K Atom, 
% 	coq.say "Atomic Key" K "for" Atom,
% 	Kons = global (indc K).

% check Cert [] Atom {{lp:Term lp:Kons}} :-
%     whd Atom [] (global (indt Prog)) Args, %% Coq-Elpi predicate!
%     coq.env.indt Prog _ _ _ _Type Kn Clauses,
% 	unfold_expert Kn Cert Cert' K,
% 	%% Use the selected constructor as key to find its
% 	%% clause in the zipped list of constructors and clauses.
% 	std.lookup {std.zip Kn Clauses} K Clause, 
% 	coq.say "Key" K "for" Atom,
% 	coq.say "Indeed" Term,
% 	% get-range (prod _ A B) Atom,
% 	Kons = global (indc K),
% 	coq.say "Still here, know " Term,
% 	% (OutTerm = (app [Kons | _] ); OutTerm = Kons),
% 	check Cert' [Clause] Atom Term,
% 	coq.say "Ok" K "with" Term.

