(* DEPENDENT "prolog"-like tactic modulo FPC for height, size and pairing thereof  -- am*)

From elpi Require Import elpi.
Require Import Arith List. Import ListNotations.
Require Import Coq.Lists.List.

Elpi Tactic dprolog.
(* Debugging symbols: RAW means no pretty printing is used for Coq terms, and
the HOAS encoding is printed. *)
(* Elpi Debug "DEBUG_KERNEL". *)
(* Elpi Debug "DEBUG_KERNEL_RAW". *)
From fpc_elpi.pbt Extra Dependency "dep-kernel.mod" as dep_kernel.
From fpc_elpi.pbt Extra Dependency "fpc-qbound.mod" as fpc_qbound.
From fpc_elpi.pbt Extra Dependency "fpc-pair.mod" as fpc_pair.

Elpi Accumulate File dep_kernel.
Elpi Accumulate File fpc_qbound.
Elpi Accumulate File fpc_pair.

Elpi Accumulate lp:{{
  solve (goal _Ctx _RawEv Goal Ev [int N]) _OutGoals :-
    coq.say "Goal:" {coq.term->string Goal},
    check (qgen (qheight N)) (go Goal Term),
    Ev = Term,
    coq.say "Proof:" {coq.term->string Ev}.
 solve (goal _Ctx _RawEv Goal Ev [str "size", int N]) _OutGoals :-
    coq.say "Goal:" {coq.term->string Goal},
    check (qgen (qsize N M_)) (go Goal Term),
    Ev = Term,
    coq.say "Proof:" {coq.term->string Ev}.
solve (goal _Ctx _RawEv Goal Ev [str "pair", int H, int S ]) _OutGoals :-
    coq.say "Goal:" {coq.term->string Goal},
    check (pair (qgen (qheight H)) (qgen (qsize S S2_ ))) (go Goal Term),
    Ev = Term,
    coq.say "Proof:" {coq.term->string Ev}.
  }}.
Elpi Typecheck. 

Inductive insert (x:nat) : list nat -> list nat -> Prop :=
i_n : insert x [] [x]
| i_s : forall y: nat, forall ys: list nat, x <= y -> insert x (y :: ys) (x :: y :: ys)
| i_c : forall y: nat, forall ys: list nat, forall rs: list nat,  y <= x -> insert x ys rs -> insert x (y :: ys) (y :: rs).

Goal insert 1 [] [1].
elpi dprolog 4.
Qed.

Goal le 0 1.
elpi dprolog 4.
Qed.
Lemma i0: insert 2 ([1])  [1;2].
elpi  dprolog 10.
Qed.
Lemma i1:  exists R, insert 2 ([0; 1])  R.
eexists.
elpi  dprolog 10. Qed.
Lemma i1i:  exists R, insert 2 ([0] ++ [1])  R.
elpi  dprolog 10.
Qed.
Print i1.
Lemma i2:  exists R, insert 2 ([0] ++ [1]) R.
eexists.
apply i_c. auto.
apply i_c. auto.
apply i_n.
Qed.

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
  elpi dprolog 10.
Qed.

Inductive append : list nat -> list nat -> list nat -> Prop :=
  anl : forall xs, append [] xs xs
 |acn : forall xs ys zs x, append xs ys zs -> append (x :: xs) ys (x :: zs).

(* Goal exists L1 L2, append L1 L2 [0;1;2;6]. *)
Goal append  [0] [1;2;6] [0;1;2;6].
  elpi dprolog 20.
Qed.

Goal exists L, append  L [1;2;6] [0;1;2;6].
  eexists.
  elpi dprolog  20.
Qed.
