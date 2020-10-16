/*
Conjecture a: forall (P : Prop), P -> P.
Conjecture an: exists (P : Prop), P /\ (not P).
The type of a is: prod `P` (sort prop) c0 \ prod `_` c0 c1 \ c0
Conjecture att :  True -> True.
	   prod `_` (global (indt «True»)) c0 \ global (indt «True»)

negation

app [global (indt «ex»), sort prop, 
  (fun `P` (sort prop) c0 \
	app [global (indt «and»), c0, app [global (const «not»), c0]])]
app
 [global (indt «and»), global (indt «True»), 
  app [global (const «not»), global (indt «True»)]]
*/

% quant
nnf (prod Name T1 T2) ( app [global (indt «ex»), T1, (fun Name T1 (c \ (NT2 c))) ]) :-
  pi x \ nnf x x -> nnf (T2 x) (NT2 x).


% ->
nnf (prod  `_` T1 T2) (app [global (indt «and»), NT1, NT2)]) :-
  !,
nnf T1 NT1, nnf T2 NT2.

% at atoms, do nothing in the antecedent, put NF in the consequent???

% may need two nnf, nnfp and nnfn for positive and negative action