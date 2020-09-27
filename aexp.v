(* Adapted from Types.v in volume  of Software foundations:
inductive defs of static and dynamic semantics of a simple arithmetic language
(first-order). Parametric definition of progress (could also do deterministm of
step and preservation) and a couple of mutants (see exercise 2 in types.v)*)

From elpi Require Import elpi.
Require Import Arith List. Import ListNotations.
 Import Coq.Lists.List.
 Require Import pbt.


Inductive tm : Type :=
| ttrue : tm
| tfalse : tm
| tif : tm -> tm -> tm -> tm
| tzero : tm
| tsucc : tm -> tm
| tpred : tm -> tm
| tiszero : tm -> tm.

Inductive typ : Type :=
|TBool : typ
|TNat : typ.

Inductive has_type : tm -> typ -> Prop :=
  | T_Tru :
        has_type ttrue TBool
  | T_Fls :
       has_type tfalse TBool
   | T_Test : forall t1 t2 t3 T,
       has_type t1 TBool ->
       has_type t2 T ->
       has_type t3 T ->
       has_type (tif  t1 t2 t3) T 
  | T_Zro :
       has_type tzero TNat
  (*! *)
  | T_Scc : forall t1,
        has_type t1 TNat ->
        has_type (tsucc t1) TNat
  (*!! test-bug *)
  (*! 
  | T_SccBool : forall t,
           has_type t TBool ->
           has_type (tsucc t) TBool
 *)
  | T_Prd : forall t1,
       has_type t1 TNat ->
       has_type (tpred t1 ) TNat
  | T_Iszro : forall t1,
       has_type t1 TNat ->
       has_type (tiszero t1) TBool.


Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : forall t, nvalue t -> nvalue (tsucc t).

Inductive bvalue : tm -> Prop :=
  | bv_t : bvalue ttrue
  | bv_f : bvalue tfalse.


  Reserved Notation "t1 '===>' t2" (at level 40).


Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ===> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ===> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ===> t1' ->
      (tif t1 t2 t3) ===> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ===> t1' ->
      (tsucc t1) ===> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ===> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ===> t1
  | ST_Pred : forall t1 t1',
      t1 ===> t1' ->
      (tpred t1) ===> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ===> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ===> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ===> t1' ->
      (tiszero t1) ===> (tiszero t1')

where "t1 '===>' t2" := (step t1 t2).


Inductive notstuck (e : tm) (Step : tm -> tm -> Prop) : Prop :=
  | p1 :   nvalue e  -> notstuck e Step
  | p2 : bvalue e -> notstuck e Step
  | ps : forall  e', Step e e' -> notstuck e Step.
  
 
Definition progress (e :tm) (Has_type : tm -> typ -> Prop) (Step : tm -> tm -> Prop):= 
    forall t, Has_type e t -> notstuck e Step.
 
(* trying to use typing directly as a generator: the property holds*)
Goal forall e, progress e has_type step.
unfold progress.
intros e t Ht.    
Fail elpi pbt (Ht)  24.
Abort.

(* a typo-like mutation*)
Module M1.

Inductive has_type : tm -> typ -> Prop :=
  | T_Tru :
        has_type ttrue TBool
  | T_Fls :
       has_type tfalse TBool
   | T_Test : forall t1 t2 t3 T,
       has_type t1 TBool ->
       has_type t2 T ->
       has_type t3 T ->
       has_type (tif  t1 t2 t3) T 
  | T_Zro :
       has_type tzero TNat
  | T_Scc : forall t1,
        has_type t1 TNat ->  has_type (tsucc t1) TNat
  | T_Prd : forall t1,
       has_type t1 TNat ->
       has_type (tpred t1 ) TNat
  | T_Iszro : forall t1,
       has_type t1 TBool ->
       has_type (tiszero t1) TNat.

End M1.

(* may have to code progress as an atom*)

Goal forall e, progress e M1.has_type step.
unfold progress.
intros e t Ht.    
Fail elpi pbt (Ht)  100 (e). (* it should find a cex:  tiszero(ttrue)
T = tnat*)
Abort.