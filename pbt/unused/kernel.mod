module kernel.

%%%%%%%%%%%%%%%%%%%%%
% Helper predicates %
%%%%%%%%%%%%%%%%%%%%%

memb X (X :: _L).
memb X (_Y :: L) :- memb X L.

get_head (prod _ _ T) Head :- get_head (T X_) Head.
get_head (app L) (app L).

%%%%%%%%%%%%%%%
% Interpreter %
%%%%%%%%%%%%%%%


interp {{True}}.

interp {{lp:G1 /\ lp:G2}} :- !, % cut to avoid unfolding /\
	interp G1,
	interp G2.

interp {{lp:G1 \/ lp:G2}} :- !, % cut to avoid unfolding \/
	interp G1;
	interp G2.

interp {{lp:G = lp:G}}.

interp (app [global (indt Prog) | _Args] as Atom) :-
%   coq.say "prog: " Prog,
%   coq.say "args: " Args,
    coq.env.indt Prog _ _ _ _Type _Kn Clauses,
	memb D Clauses,
	get_head D Atom,
%	  coq.say "selected: " D,
	backchain D Atom.


% differentiating between dep and non-dep products  -AM 
backchain {{lp:G -> lp:D}} A :-
	  !,
	  backchain D A,
%	   coq.say "imp-l: " D,
	  interp G.
backchain (prod _ _Ty (x\ D x)) A :-
%	  !,
%	   coq.say "backchain : " (D X),
	  backchain (D X_) A.

backchain A A :- !. % coq.say "proven: " A.


%%%%%%%%%%%
% Checker %
%%%%%%%%%%%


% check _Cert (go (sort _)). %% removed since we use impL -am
% check _Cert (go {{nat}}).

% check Cert (go Type) :- 
%   coq.term->string Type String,
%   coq.say "check" Cert "go" String, fail.
% 
% check Cert (bc T1 T2) :- 
%   coq.term->string T1 S1,
%   coq.term->string T2 S2,
%   coq.say "check" Cert "bc" S1 S2, fail.

check Cert (go {{True}}) :-
	tt_expert Cert.

check Cert (go {{lp:G = lp:G}}) :-
	eq_expert Cert.

check Cert (go {{lp:G1 /\ lp:G2}}):-
  and_expert Cert Cert1 Cert2,
  check Cert1 (go G1),
  check Cert2 (go G2).

check Cert (go {{lp:G1 \/ lp:G2}}) :-
	or_expert Cert Cert' Choice,
	(
		(Choice = left, check Cert' (go G1))
	;
		(Choice = right, check Cert' (go G2))
	).

% atomic case
check Cert (go (app [global (indt Prog) | _Args ] as Atom)) :-
    coq.env.indt Prog _ _ _ _Type Kn Clauses,
	unfold_expert Kn Cert Cert' K,
	%% Use the selected constructor as key to find its
	%% clause in the zipped list of constructors and clauses.
	std.lookup {std.zip Kn Clauses} K Clause, 
	% coq.say "Key" K "for" Atom,
	check Cert' (bc Clause Atom).

%% Perform simple reduction in the head
check Cert (go (app [(fun A B C)| Args])) :-
  coq.mk-app (fun A B C) Args App,
  check Cert (go App).

% backchaining
% usual diff dep. vs non-dep
check Cert (bc A A) :-
      !,
      tt_expert Cert.
check Cert (bc {{lp:Ty1 ->  lp:Ty2}} Goal) :-
      !,
        prod_expert Cert Cert1 Cert2,
	  check Cert1 (bc Ty2  Goal),
	    check Cert2 (go Ty1).

check Cert (bc (prod _ _Ty1 (x\ D x)) Goal) :-
      !,
  prod_clerk Cert Cert1,
  check Cert1 (bc (D X_) Goal).
