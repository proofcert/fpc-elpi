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

Elpi Db hints.db lp:{{ 
  type hint term -> term -> prop.
}}.

Elpi Command print_db.
Elpi Accumulate Db hints.db.
Elpi Accumulate lp:{{
  main [] :- std.findall (hint Term_ Type_) L, !, coq.say "The Db contains" L.
}}.

Elpi Command add_db.
Elpi Accumulate Db hints.db.
Elpi Accumulate lp:{{
  main [trm Term] :-
    coq.typecheck Term Type ok,
    % coq.say "Type" Type,
    coq.elpi.accumulate _ "hints.db" (clause _ _ (hint Term Type)).
}}.
Elpi Typecheck.

Elpi Tactic dprolog.
Elpi Accumulate File "pbt/dep-kernel.mod".
Elpi Accumulate File "pbt/fpc-qbound.mod".
Elpi Accumulate File "pbt/fpc-pair.mod".
Elpi Accumulate Db hints.db.


 Elpi Query interp {{lp:G = lp:G}}.
 Elpi Bound Steps 1000000.
Inductive insert (x:nat) : list nat -> list nat -> Prop :=
(* i_n : insert x [] [x] *)
 i_s : forall y: nat, forall ys: list nat, x <= y -> insert x (y :: ys) (x :: y :: ys)
| i_c : forall y: nat, forall ys: list nat, forall rs: list nat,  y<=x -> insert x ys rs -> insert x (y :: ys) (y :: rs).

Axiom InsAx : forall x, insert x [] [x].

Elpi add_db (InsAx).
Elpi print_db.

(* Elpi Trace. *)
Goal exists l, insert 1 [] l.
eexists.
elpi dprolog 10.
Show Proof.
Qed.

Module test.
Theorem help: forall n m, m <= n -> n > m.
Admitted.


Inductive insert (x:nat) : list nat -> list nat -> Prop :=
 i_n : insert x [] [x] 
| i_s : forall y: nat, forall ys: list nat, y > x -> insert x (y :: ys) (x :: y :: ys)
| i_c : forall y: nat, forall ys: list nat, forall rs: list nat,  y<=x -> insert x ys rs -> insert x (y :: ys) (y :: rs).

End test.

Elpi add_db (test.help).
Goal exists l, test.insert 3 [1;4;8] l.
eexists.

elpi dprolog 10.

Goal insert 1 [] [1].
elpi dprolog 10.
Qed.
Lemma i1:  exists R, insert 2 [0;1] R.
elpi  dprolog 10.
Qed.
Lemma i2:  exists R, insert 2 [0;1] R.
eexists.
apply i_c.
apply i_c.
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
elpi prolog  3.
apply onl.
Restart.
eexists.
elpi dprolog 10.
Qed.

 Goal ordered [0;1;2;6].
   elpi prolog  10.
   Fail elpi prolog size 10.

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
 elpi dprolog 20.
Qed.

