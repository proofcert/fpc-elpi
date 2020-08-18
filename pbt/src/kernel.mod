module kernel.

%%%%%%%%%%%%%%%%%%%%%
% Helper predicates %
%%%%%%%%%%%%%%%%%%%%%

memb X (X :: _L).
memb X (_Y :: L) :- memb X L.

%%%%%%%%%%%%%%%
% Interpreter %
%%%%%%%%%%%%%%%

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
 % coq.say "prog: " Prog,
  % coq.say "args: " Args,
    coq.env.indt Prog _ _ _ _Type _Kn Clauses,
	memb D Clauses,
%	 coq.say "selected: " D
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

check Cert (sort _) :-
	tt_expert Cert.
check Cert {{nat}} :-
	tt_expert Cert.
check Cert {{True}} :-
	tt_expert Cert.

check Cert {{lp:G = lp:G}} :-
	eq_expert Cert.

check Cert {{lp:G1 /\ lp:G2}} :-
	and_expert Cert Cert1 Cert2,
	check Cert1 G1,
	check Cert2 G2.

check Cert {{lp:G1 \/ lp:G2}} :-
	or_expert Cert Cert' Choice,
	(
		(Choice = left, check Cert' G1)
	;
		(Choice = right, check Cert' G2)
	).

% check Cert (some G) :-
% 	some_expert Cert Cert' T,
% 	check Cert' (G T).

% check Cert (nabla G) :-
% 	pi x\ check Cert (G x).

% interp (app [global (indt Prog) | Args] as Atom) :-
%     coq.env.indt Prog _tt _uhm _mah Type Kn Clauses,
% 	memb G Clauses,
% 	backchain G Atom.

check Cert (app [global (indt Prog) | _Args] ) :-
    coq.env.indt Prog _ _ _ _Type Kn Clauses,
	unfold_expert Clauses Cert Cert' K,
	%% Use the selected constructor as key to find its
	%% clause in the zipped list of constructors and clauses.
	std.lookup {std.zip Kn Clauses} K G, 
	check Cert' G.
