(*"prolog"-like tactic modulo FPC for height, size and pairing thereof  -- am*)

From elpi Require Import elpi.
Require Import Arith List. Import ListNotations.
Require Import Coq.Lists.List.

Elpi Tactic prolog.
Elpi Accumulate File "pbt/src/kernel.mod".
Elpi Accumulate File "pbt/src/fpc-qbound.mod".
Elpi Accumulate File "pbt/src/fpc-pair.mod".


Elpi Accumulate lp:{{
  solve [str "height" , int N]  [goal _Ctx _Ev Goal _W] _OutGoals :-
    coq.say "Goal:" {coq.term->string Goal},
    check (qgen (qheight N)) (go Goal).

  solve [str "size", int N, int M] [goal _Ctx _Ev Goal _W] _OutGoals :-
    coq.say "Goal:" {coq.term->string Goal},
    check (qgen (qsize N M )) (go Goal).
  
  solve [str "pair", int H, int S1, int S2] [goal _Ctx _Ev Goal _W] _OutGoals :-
    coq.say "Goal:" {coq.term->string Goal},
    check (pair (qgen (qheight N)) (qgen (qsize S1 S2 ))) (go Goal).

  }}. 
Elpi Typecheck.

Elpi Tactic dprolog.
Elpi Accumulate File "pbt/src/dep-kernel.mod".
Elpi Accumulate File "pbt/src/fpc-qbound.mod".
Elpi Accumulate File "pbt/src/fpc-pair.mod".

Elpi Accumulate lp:{{
  solve [int N] [goal _Ctx Ev Goal _Who] _OutGoals :-
    coq.say "Goal:" {coq.term->string Goal},
    check (qgen (qheight N)) (go Goal Term),
    Ev = Term.
  }}.
Elpi Typecheck.

Elpi Bound Steps 100000.


 Inductive ordered : list nat -> Prop :=
onl : ordered []
| oss : forall x : nat, ordered [x]
| ocn : forall (x y : nat) (l : list nat),
     ordered (y :: l) -> x <= y -> ordered (x :: y :: l).

 Goal ordered [0;1;2;6].
   elpi prolog height 40.
   Restart.
   Fail elpi prolog size 100 N .
   elpi dprolog 60.
   Qed.

