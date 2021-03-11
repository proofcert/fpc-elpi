(** Some programming with dependent types, based on Adam's book *)

Require Import Arith Bool List.
Require Coq.extraction.Extraction.
Extraction Language OCaml.
(** the standard fix point def*)
Fixpoint len (A : Set)(l : list A) : nat :=
  match l with
  | nil => 0
  | _ :: l' => S (len _ l')
                 end.
Print len.

(** Indexed lists*)
Set Implicit Arguments.

(** we assume some parameters to make declarations shorter:*)
Section ilist.
  Variable A : Set.
  Variable a : A.


(** the type of lists of length n:*)  
Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

Check Nil. 
Check (Cons a Nil).

Print ilist.

(** build a list of [n] copies of [a] *)

Fixpoint repeat n  : ilist n :=
  match n with
      | 0 => Nil
      | S m => Cons a (repeat m)
  end.

Print repeat.
Eval compute  in  repeat 5.

Fixpoint app n1 n2 (ls1 : ilist n1) (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 with
      | Nil => ls2
      | Cons  x ls1' => Cons x (app ls1' ls2)
    end.

Check app.
Print app.

Definition hd n (ls : ilist (S n)) : A :=
    match ls with
      | Cons  h _ => h
    end.

Check hd.


Definition tl n (ls : ilist (S n)) : (ilist n) :=
    match ls with
      | Cons   _ t => t
    end.

Check tl.


Fixpoint snoc n (ls : ilist n) (x : A) : ilist (S n) :=
    match ls with
      | Nil => Cons x Nil
      | Cons  y ls' => Cons y (snoc ls' x)
    end.

Fixpoint rev n (ls : ilist n)  : ilist n :=
    match ls with
      | Nil => Nil
      | Cons  x ys => (snoc (rev  ys) x)
    end.

Print rev.

(** Why didn't we define [rev] via [app]? Because it is not immediate:*)

Fail Fixpoint revapp n (ls : ilist n)  : ilist n :=
  match ls in (ilist n0)   return (ilist n0 ) with
      | Nil => Nil
      | Cons  x ys => app (revapp  ys) (Cons x Nil)
    end.
(* The term "app (revapp n0 ys) (Cons x Nil)" has type "ilist (n0 + 1)" while it is expected to have type "ilist (S n0)".*)

(** Since types depend on terms, namely [nats], type inference entails some theorem proving, here 
the easy theorem that [n0 + 1 = S n0]. The former is what the type of [app] requires, but the latter
is what the type of [rev] offers. In general, these lemmas may be arbitrarily difficult. They derive from the conversion rule
in the type theory of Coq --- roughly

[[[

Gamma |-  m : A t       Gamma |- t == s
-------------------------------------------------------
         Gamma |- m : A s 

]]]


Luckily we can use the [Program] package, which let us
_prove_ the additional proof obligations.

Note (or not) that we have to be more explicit about the
return type of each branch of the pattern matching.
*)

Program Fixpoint revapp n (ls : ilist n)  : ilist n :=
  match ls in (ilist n0)   return (ilist n0 ) with
      | Nil => Nil
      | Cons  x ys => app (revapp  ys) (Cons x Nil)
  end.
Obligation 1.
rewrite <- plus_n_Sm. rewrite <- plus_n_O. reflexivity.
Defined.
End ilist.



(*
Other types as spec that we'd like to express

- Red and black trees, where the invariant is preserved by the type itself
*)





Inductive color : Set := Red | Black.

Inductive rbtree : color -> nat -> Set :=
| Leaf : rbtree Black 0
| RedNode : forall n, rbtree Black n -> nat -> rbtree Black n -> rbtree Red n
| BlackNode : forall c1 c2 n, rbtree c1 n -> nat -> rbtree c2 n -> rbtree Black (S n).



(** A value of type [rbtree c d] is a red-black tree whose root has
color [c] and that has black depth [d].  The latter property means
that there are exactly [d] black-colored nodes on any path from the
root to a leaf. *)

(** Types that are more informative, allowing us to express the specification of the function
in the type signature. We consider a simple example: predecessor *)

(** the standard one *)
Definition pred (n : nat) : nat :=
  match n with
    | 0 => 0
    | S n' => n'
  end.

(** a useful lemma *)
Lemma zgtz: 0 > 0 -> False.
  intro.  inversion H.
Qed.

(** strenghening the precondition: *)
Definition pred_s1 (n : nat) : n > 0 -> nat :=
  match n with
    |0 => fun pf : 0 > 0 =>
            match zgtz pf with end
    | S n' => fun _ => n'
  end.


Print pred_s1.
(** Let's see what it looks like in OCaml:*)
Extraction pred_s1.

(** The _irrelevant_ proving part has been erased.*)

(** we can derive the same definition interactively. Note full stop after the type that
enters proving mode. *)

Definition pred_ss (n : nat) : n > 0 -> nat.
destruct n.
- intros. apply  zgtz in H. destruct H.
- intros. exact n.
Defined.
Print pred_ss.
Extraction pred_ss.

(** or we can use the [Program] library and*)
Program Definition pred_sp1 (n : nat)(pf:  n > 0 ) :  nat :=
    match n with
    | O => _
    | S n' => n'
    end.
Obligation 1.
apply zgtz in pf.exfalso. assumption.
Defined.

Extraction pred_s1.


(* The strongest spec, where we use subset types to say exactly what [pred] does:*)

Program Definition pred_strong6 (n : nat) (_ : n > 0) : {m : nat | n = S m} :=
  match n with
    | O => _
    | S n' => n'
  end.
Obligation 1.
intros. apply zgtz in H. exfalso. assumption.
Defined.

