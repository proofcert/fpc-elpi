From elpi Require Import elpi.
Require Import Arith List. Import ListNotations.
Require Import Coq.Lists.List.

Inductive append : list nat -> list nat -> list nat -> Prop :=

anl : forall xs, append [] xs xs
|acn: forall xs ys zs x, 
append xs ys zs -> append (x :: xs) ys (x :: zs).

Hint Constructors append.
Goal append [1;2] [3;4] [1;2;3;4].
auto.
Qed.

Elpi Command pbt.
Elpi Accumulate File "pbt/src/kernel.mod".
Elpi Typecheck.
Elpi Query lp:{{
  interp {{append [1;2] [3;4] [1;2;3;4].}}.
  }}.

Inductive rev : list nat -> list nat -> Prop :=
r1nl : rev [] []
| r1c : forall (x: nat) (l ts rs : list nat),
       rev l ts -> append ts [x] rs -> rev (x  :: l) rs.

Elpi Query lp:{{
        interp {{rev  [1;2] [2;1].}}.
        }}.       
(* iterative*)
Inductive revA : list nat -> list nat -> list nat -> Prop :=
rnl : forall acc, revA [] acc acc
| rc : forall (x: nat) (l acc rs : list nat),
       revA l (x :: acc) rs  -> revA (x  :: l) (x :: acc) rs.

Inductive rev2 : list nat -> list nat -> Prop :=
r: forall xs ys, revA xs [] ys -> rev2 xs ys.

Goal rev ([1;2]) ([2;1]).
Abort.