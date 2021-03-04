(* NON dependent "prolog"-like tactic modulo FPC for height, size and pairing thereof

OBSOLETE: go to dprolog.v*)

From elpi Require Import elpi.
Require Import Arith List. Import ListNotations.
Require Import Coq.Lists.List.

Elpi Tactic prolog.
Elpi Accumulate File "pbt/kernel.mod".
Elpi Accumulate File "pbt/fpc-qbound.mod".
Elpi Accumulate File "pbt/fpc-pair.mod".


Elpi Accumulate lp:{{
  solve [int N]  [goal _Ctx _Ev Goal _W] _OutGoals :-
    coq.say "Goal:" {coq.term->string Goal},
    check (qgen (qheight N)) (go Goal).

% leaving the lower bound open 
  solve [str "size", int N] [goal _Ctx _Ev Goal _W] _OutGoals :-
    coq.say "Goal:" {coq.term->string Goal},
    check (qgen (qsize N M_ )) (go Goal).  
  
  solve [str "pair", int H, int S] [goal _Ctx _Ev Goal _W] _OutGoals :-
    coq.say "Goal:" {coq.term->string Goal},
    check (pair (qgen (qheight H)) (qgen (qsize S S2_ ))) (go Goal).

  }}. 
Elpi Typecheck.



 Elpi Query interp {{lp:G = lp:G}}.
 Elpi Bound Steps 1000000.

Inductive insert (x:nat) : list nat -> list nat -> Prop :=
i_n : insert x [] [x]
| i_s : forall y: nat, forall ys: list nat, x <= y -> insert x (y :: ys) (x :: y :: ys)
| i_c : forall y: nat, forall ys: list nat, forall rs: list nat,  insert x ys rs -> insert x (y :: ys) (y :: rs).

Goal insert 1 [] [1].
elpi dprolog 10.
Qed.
