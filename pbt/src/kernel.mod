module kernel.

%%%%%%%%%%%%%%%%%%%%%
% Helper predicates %
%%%%%%%%%%%%%%%%%%%%%

memb X (X :: L).
memb X (Y :: L) :- memb X L.

%%%%%%%%%%%%%%%
% Interpreter %
%%%%%%%%%%%%%%%

interp {{True}}.
interp {{nat}}.
interp (sort _).

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

% interp (prod _ Ty G) :-
%   cl Ty =>
%   interp (G X).

% interp A :-
% 	cl Ty,
% 	backchain Ty A.
interp (app [global (indt Prog) | Args] as Head) :-
    coq.env.indt Prog _ _ _ Type Kn Types,
	memb G Types,
	backchain G Head.

interp G :- cl C Var, backchain C G.
backchain A B :- coq.say "backchain" A B, fail.
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

interp (app [global (indt Prog) | Args] as Head) :-
    coq.env.indt Prog _tt _uhm _mah Type Kn Types,
	memb G Types,
	backchain G Head.

% The unfold rule lets the expert inspect the available clauses (this should
% be done with great care, ideally limiting the information to a list of names,
% set and immutable) and can restrict their selection by name.
check Cert (app [global (indt Prog) | Args] as Head) :-
    coq.env.indt Prog _ _ _ Type Kn Types,
	unfold_expert Types Cert Cert' K,
	%% Use the selected constructor as key to find its
	%% clause in the zipped list of constructors and clauses.
	std.lookup {std.zip Kn Types} K G, 
	check Cert' G.