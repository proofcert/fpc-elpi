(* A toy examples to mix comuptation and deduction *)

Inductive tm : Type :=
  | C : nat -> tm         (* Constant *)
  | P : tm -> tm -> tm.   (* Plus *)

Reserved Notation " t '===>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) ===> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ===> t1' ->
      P t1 t2 ===> P t1' t2
  | ST_Plus2 : forall n1 t2 t2',
      t2 ===> t2' -> 
      P (C n1) t2 ===> P (C n1) t2'

  where " t '===>' t' " := (step t t').



Goal
      P 
        (P (C 3) (C 0))
        (P (C 2) (C 4))
      ===>
      P 
        (C 3)
        (P (C 2) (C 4)).
Proof.
  apply ST_Plus1. apply ST_PlusConstConst.  Qed.
