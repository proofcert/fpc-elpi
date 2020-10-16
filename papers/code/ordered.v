From elpi Require Import elpi.

Require Import Arith List. Import ListNotations.
Require Import Coq.Lists.List.

Inductive ordered : list nat -> Prop :=
	onl : ordered []
  | oss : forall x : nat, ordered [x]
  | ocn : forall (x y : nat) (l : list nat),
         ordered (y :: l) -> x <= y -> ordered (x :: y :: l).
Elpi Command constructors.
Elpi Query lp:{{
  coq.locate "ordered" GR,   coq.say "ordered is:" GR,
  coq.env.typeof GR Ty, coq.say "The type of ordered is:" Ty.  
}}.



Elpi Command constructors_num.
Elpi Accumulate lp:{{
    coq.locate "ordered" (indt GR),
    coq.env.indt GR _ _ _ _ Kn _,   % get the names of the constructors
    coq.say Kn. 
 }}.
Elpi Typecheck.
     
Inductive insert (x : nat) : list nat -> list nat -> Prop:=
 | inil: insert  x [] [x]
 |ic1 : forall y ys, x <= y -> insert x (y :: ys) (x :: y :: ys)
 |ic2: forall y ys ns, y < x -> insert x ys ns ->  insert x (y :: ys) (y :: ns).

 Goal exists L, insert 3 ( 1 :: 2 :: nil) L.
 eexists.
 apply ic2.
 - auto.
 - apply ic2.
  + auto.
  + constructor.
  Qed.
  
  Conjecture pres: forall x xs ys, ordered ys -> insert x xs ys -> ordered ys.
  