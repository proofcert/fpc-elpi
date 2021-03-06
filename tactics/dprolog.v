(* DEPENDENT "prolog"-like tactic modulo FPC for height, size and pairing thereof  -- am*)

From elpi Require Import elpi.
Require Import Arith List. Import ListNotations.
Require Import Coq.Lists.List.


Elpi Tactic dprolog.
Elpi Accumulate File "pbt/dep-kernel.mod".
Elpi Accumulate File "pbt/fpc-qbound.mod".
Elpi Accumulate File "pbt/fpc-pair.mod".

Elpi Accumulate lp:{{
  solve [int N] [goal _Ctx Ev Goal _Who] _OutGoals :-
    coq.say "Goal:" {coq.term->string Goal},
    check (qgen (qheight N)) (go Goal Term),
    Ev = Term,
    coq.say "Proof:" {coq.term->string Ev}.
 solve [str "size", int N] [goal _Ctx Ev Goal _Who] _OutGoals :-
    coq.say "Goal:" {coq.term->string Goal},
    check (qgen (qsize N M_)) (go Goal Term),
    Ev = Term,
    coq.say "Proof:" {coq.term->string Ev}.
solve [str "pair", int H, int S ] [goal _Ctx Ev Goal _Who] _OutGoals :-
      coq.say "Goal:" {coq.term->string Goal},
    check (pair (qgen (qheight H)) (qgen (qsize S S2_ ))) (go Goal Term),
    Ev = Term,
    coq.say "Proof:" {coq.term->string Ev}.
  }}.
 Elpi Typecheck. 

 Elpi Bound Steps 1000000.

Inductive insert (x:nat) : list nat -> list nat -> Prop :=
i_n : insert x [] [x]
| i_s : forall y: nat, forall ys: list nat, x <= y -> insert x (y :: ys) (x :: y :: ys)
| i_c : forall y: nat, forall ys: list nat, forall rs: list nat,  y <= x -> insert x ys rs -> insert x (y :: ys) (y :: rs).

Goal insert 1 [] [1].
elpi dprolog 10.
Qed.
Lemma i1:  exists R, insert 2 ([0] ++ [1])  R.
elpi  dprolog 10.
Qed.
Print i1.
Lemma i2:  exists R, insert 2 ([0] ++ [1]) R.
eexists.
apply i_c. auto.
apply i_c. auto.
apply i_n.
Qed.
Print i2.
Print le.
 Inductive ordered : list nat -> Prop :=
onl : ordered []
| oss : forall x : nat, ordered [x]
| ocn : forall (x y : nat) (l : list nat),
     ordered (y :: l) -> x <= y -> ordered (x :: y :: l).

Goal exists Xs, ordered Xs.
eexists.
elpi dprolog 10.
Qed.

 Goal ordered [0;1;2;6].
   
   elpi dprolog 20.
   Qed.

   Inductive append : list nat -> list nat -> list nat -> Prop :=
   anl : forall xs, append [] xs xs
   |acn : forall xs ys zs x, 
        append xs ys zs -> append (x :: xs) ys (x :: zs).

  (* Goal exists L1 L2, append L1 L2 [0;1;2;6]. *)
  Goal append  [0] [1;2;6] [0;1;2;6].
  elpi dprolog 20.
Qed.

 Goal exists L, append  L [1;2;6] [0;1;2;6].
 eexists.
 elpi dprolog  20.
 Qed.
