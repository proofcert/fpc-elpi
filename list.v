(* moving list to poly*)
Require Import Arith List. Import ListNotations.
 Import Coq.Lists.List.
 

 Inductive ordered : list nat -> Prop :=
onl : ordered []
| oss : forall x : nat, ordered [x]
| ocn : forall (x y : nat) (l : list nat),
     ordered (y :: l) -> x <= y -> ordered (x :: y :: l).

(* the following is the bugged version*)
Inductive ordered_bad : list nat -> Prop :=
onlb : ordered_bad []
| ossb : forall x : nat, ordered_bad [x]
| ocnb : forall (x y : nat) (l : list nat),
            ordered_bad l  -> x <= y -> ordered_bad (x:: y :: l).         

Inductive append {A : Set}: list A -> list A -> list A -> Prop :=
anl : forall xs, append [] xs xs
|acn : forall xs ys zs x, 
     append xs ys zs -> append (x :: xs) ys (x :: zs).

Inductive rev {A : Set} : list A -> list A -> Prop :=
r1nl : rev [] []
| r1c : forall (x: A) (l ts rs : list A),
   append ts [x] rs -> rev l ts -> rev (x  :: l) rs.

(* iterative*)
Inductive revA {A : Set} : list A -> list A -> list A -> Prop :=
rnl : forall acc, revA [] acc acc
| rc : forall (x : A) (l acc rs : list A),
   revA l (x :: acc) rs  -> revA (x  :: l) acc rs.

Inductive rev2 {A : Set}: list A -> list A -> Prop :=
r: forall xs ys, revA xs [] ys -> rev2 xs ys.

Inductive is_nat : nat -> Prop :=
nz: is_nat 0
| ns: forall n: nat, is_nat n -> is_nat (S n).

Inductive is_natlist : list nat -> Prop :=
nl: is_natlist []
| nlcons: forall l: list nat, forall n:nat, is_natlist l ->  is_nat n -> is_natlist (cons n l).

Inductive insert (x:nat) : list nat -> list nat -> Prop :=
i_n : is_nat x -> insert x [] [x]
| i_s : forall y: nat, forall ys: list nat, x <= y -> insert x (y :: ys) (x :: y :: ys)
| i_c : forall y: nat, forall ys: list nat, forall rs: list nat, x > y -> insert x ys rs -> insert x (y :: ys) (x :: rs).

