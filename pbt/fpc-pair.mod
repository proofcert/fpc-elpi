module fpc-pair.

%%%%%%%%%%%%%%%%%%%%%%%
% Certificate pairing %
%%%%%%%%%%%%%%%%%%%%%%%

tt_expert (pair C1 C2) :-
	tt_expert C1,
	tt_expert C2.

eq_expert (pair C1 C2) :-
	eq_expert C1,
	eq_expert C2.

and_expert (pair C1 C2) (pair C1' C2') (pair C1'' C2'') :-
	and_expert C1 C1' C1'',
	and_expert C2 C2' C2''.

or_expert (pair C1 C2) (pair C1' C2') Ch :-
	or_expert C1 C1' Ch,
	or_expert C2 C2' Ch.

prod_expert (pair C1 C2) (pair C1' C2') :-
	prod_expert C1 C1',
	prod_expert C2 C2'.
imp_expert (pair C1 C2) (pair C1' C2') (pair C1'' C2'') :-
	imp_expert C1 C1' C1'',
	imp_expert C2 C2' C2''.
prod_clerk (pair C1 C2) (pair C1' C2') :-
	   prod_clerk C1 C1',
	   prod_clerk C2 C2'.

% some_expert (pair C1 C2) (pair C1' C2') T :-
% 	some_expert C1 C1' T,
% 	some_expert C2 C2' T.

unfold_expert Gs (pair C1 C2) (pair C1' C2') Id :-
	unfold_expert Gs C1 C1' Id,
	unfold_expert Gs C2 C2' Id.