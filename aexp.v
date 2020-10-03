(* Adapted from Types.v in volume  of Software foundations:
inductive defs of static and dynamic semantics of a simple arithmetic language
(first-order). Parametric definition of progress and preservation
 and some mutants (see exercise 2 in types.v)*)

From elpi Require Import elpi.
Require Import Arith List. Import ListNotations.
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
  | T_Scc : forall t1,
        has_type t1 TNat ->
        has_type (tsucc t1) TNat

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
  

 (*parametric defs of progress and preservation *) 

 Inductive notstuck (e : tm) (Step : tm -> tm -> Prop) : Prop :=
 | pn : nvalue e  -> notstuck e Step
 | pb : bvalue e -> notstuck e Step
 | ps e' : Step e e' -> notstuck e Step.


 Definition progress (e :tm) (Has_type : tm -> typ -> Prop) (Step : tm -> tm -> Prop):= 
    forall t, Has_type e t -> notstuck e Step.

Definition preservation (e e':tm) (Has_type : tm -> typ -> Prop) (Step : tm -> tm -> Prop):= 
    forall t, Step e e' -> Has_type e t -> Has_type e' t.

Definition deterministic {X Y: Type} (R : X -> Y -> Prop) :=
        forall (x : X) (y1 y2 : Y), R x y1 -> R x y2 -> y1 = y2.

(* trying to use typing directly as a generator: the property holds*)
Goal forall e, progress e has_type step.
unfold progress.
intros e t Ht.    
Fail elpi pbt (Ht) (True) 15 (e).
Abort.

(*variation 6*)
Module M6.
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
        has_type t1 TNat ->
        has_type (tsucc t1) TNat
  | T_Prd : forall t1,
       has_type t1 TNat ->
       has_type (tpred t1 ) TNat
  | T_Prd_B6: has_type (tpred tzero) TBool(*bug6*)
  | T_Iszro : forall t1,
       has_type t1 TNat ->
       has_type (tiszero t1) TBool.


End M6.


(* pres should fail for M6: M = tpred(tzero) M' = tzero T = tBool
[Note: it loops if step is the generator*)


Goal forall e e', preservation e e' M6.has_type step.
unfold preservation.
intros e e' t Hs Ht.    
elpi pbt (Ht) (Hs)  20 (e). 
Abort.

(* Next should fail with same cex
E = tpred(tzero)
T1 = tnat
T2 = tbool*)

Elpi Bound Steps 10000.

Goal deterministic M6.has_type.
unfold deterministic.
intros.
Fail elpi pbt (H ) (H0)  20 (x). 
Abort.
(*Elpi Query lp:{{
  check (qgen (qheight 10)) (go {{M6.has_type (tpred tzero) TBool}}).
  }}. 


*)

(* a typo-like mutation*)
Module Mty.

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

End Mty.



Elpi Bound Steps 10000.
Goal forall e, progress e Mty.has_type step.
unfold progress.
intros e t Ht.    
elpi pbt (Ht) (True) 5 (e). (* it finds cex:  tiszero(ttrue)
T = tnat*)
Abort.
