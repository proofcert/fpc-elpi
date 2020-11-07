(* Intrinsically typed version of aexp*)

 From elpi Require Import elpi.
 Require Import Arith List. Import ListNotations.

Require Import Coq.Program.Equality.
 Require Import pbt.
 

Inductive typ : Type :=
       |TBool : typ
       |TNat : typ.

 Inductive tm : typ -> Type :=
 | ttrue : tm TBool
 | tfalse : tm TBool
 | tif T: tm  TBool-> tm T -> tm T -> tm T
 | tzero : tm TNat
 | tsucc : tm TNat -> tm TNat
 | tpred : tm TNat-> tm TNat
 | tiszero : tm TNat-> tm TBool.

 Inductive value : forall {T:typ}, tm T -> Prop :=
   | iNz : value tzero
   | invs : forall t, value t -> value (tsucc t)
   | ibv_t : value ttrue
   | ibv_f : value tfalse.

 

 Inductive step : forall {T : typ}, tm T -> tm T -> Prop :=
   | ST_IfTrue : forall  T (t1  t2 : tm T),
       step (tif _ ttrue t1 t2) t1
   | ST_IfFalse : forall T (t1 t2 : tm T),
       step (tif _ tfalse t1 t2) t2
    | ST_If (T : typ): forall (t1 : tm TBool) t1' (t2 t3 : tm T),
       step t1 t1' -> step (tif _ t1 t2 t3) (tif _ t1' t2 t3)
   
   | ST_Succ : forall t1 t1',
       step t1 t1' -> step (tsucc t1) (tsucc t1')
   | ST_PredZero : step (tpred tzero)  tzero
   | ST_PredSucc : forall t1,
       value t1 -> step (tpred (tsucc t1)) t1
   | ST_Pred : forall t1 t1',
       step t1 t1' -> step (tpred t1) (tpred t1')
   | ST_IszeroZero : step (tiszero tzero)  ttrue
   | ST_IszeroSucc : forall t1,
        value t1 ->  step (tiszero (tsucc t1)) tfalse
   | ST_Iszero : forall t1 t1',
       step t1  t1' -> step (tiszero t1) (tiszero t1').
   
 
  (*parametric defs of progress *) 
 
  Inductive progress {T : typ }(e : tm T) (Step : tm T -> tm T -> Prop) : Prop :=
  | pb : value e  -> progress e Step
  | ps e' : Step e e' -> progress e Step.
 
 
 (* progress holds*)
 Goal forall T (e : tm T), progress e  step.
 intros.    
 Fail elpi pbt (e) (True) 5 (e).
 Abort.
 
 
 Module M3.
 (* variation 3: failure of step det *)
 
 Reserved Notation "t1 '====>' t2" (at level 40).
 
 Inductive step : forall {T: typ}, tm T -> tm T -> Prop :=
   | ST_IfTrue : forall T t1 t2,
       (tif T ttrue t1 t2) ====> t1
   | ST_IfFalse : forall T t1 t2,
       (tif T tfalse t1 t2) ====> t2
   | ST_If : forall T t1 t1' t2 t3,
       t1 ====> t1' ->
       (tif T t1 t2 t3) ====> (tif T t1' t2 t3)
   | ST_Succ : forall t1 t1',
       t1 ====> t1' ->
       (tsucc t1) ====> (tsucc t1')
   | ST_PredZero :
       (tpred tzero) ====> tzero
   | ST_PredSucc : forall t1,
       value t1 ->
       (tpred (tsucc t1)) ====> t1
   | ST_Pred : forall t1 t1',
       t1 ====> t1' ->
       (tpred t1) ====> (tpred t1')
   | ST_IszeroZero :
       (tiszero tzero) ====> ttrue
   | ST_IszeroSucc : forall t1,
        value t1 ->
       (tiszero (tsucc t1)) ====> tfalse
   | ST_Iszero : forall t1 t1',
       t1 ====> t1' ->
       (tiszero t1) ====> (tiszero t1')
  | ST_Funny2 : forall T t1 t2 t2' t3, (*bug*)
            t2 ====> t2' ->
            (tif T t1 t2 t3) ====> (tif T  t1 t2' t3)
                    
 where "t1 '====>' t2" := (step t1 t2).
 
 End M3.  
 

 
 (* (tif tfalse ?e1 ?e0 = tif ttrue ?e0 ?e6) 
 Finds the cex, albeit not fully instantiated: should have a is_exp generetor
 *)
 Goal  forall (T : typ) (x y1 y2 : tm T ), M3.step x y1 -> M3.step  x y2 -> y1 = y2.
 
 intros.
 elpi pbt (H ) (H0)  5 (x). 
 Abort.
 
 (* we should do this with dep kernel*)
 Inductive is_tm : forall {T}, tm T -> Prop :=
   | I_Tru :        is_tm ttrue 
   | I_Fls :       is_tm tfalse 
    | I_Test : forall T t1 t2 t3 ,
        is_tm t1 ->
        is_tm t2  ->
        is_tm t3  ->
        is_tm (tif  T t1 t2 t3)  
   | I_Zro :       is_tm tzero 
   | I_Scc : forall t1,
         is_tm t1  ->        is_tm (tsucc t1) 
   | I_Prd : forall t1,
        is_tm t1  ->       is_tm (tpred t1 ) 
   | I_Iszro : forall t1,
        is_tm t1  ->       is_tm (tiszero t1) .
 
 
 Goal forall T (e1 e2 e3  : tm T), is_tm e1 ->  M3.step e1 e2 -> M3.step e1 e3 -> e2 = e3.
   intros.
   elpi pbt (H) (H0 /\ H1) 15 (e2).
 Abort.
 
 
 
 (* a typo-like mutation -- modules don't work
 when changing tm, so repeat the whole thing:

actually, preservation fails, so step cannot be formulated*)
 
 (*
 Inductive tmb : typ -> Type :=
 | ttrueb : tmb TBool
 | tfalseb : tmb TBool
 | tifb T: tmb  TBool-> tmb T -> tmb T -> tmb T
 | tzerob : tmb TNat
 | tsuccb : tmb TNat -> tmb TNat
 | tpredb : tmb TNat-> tmb TNat
 | tiszerob : tmb TBool-> tmb TNat. (*bug*)

 Inductive valueb : forall {T:typ}, tmb T -> Prop :=
   | iNzb : valueb tzerob
   | invsb : forall t, valueb t -> valueb (tsuccb t)
   | ibvt : valueb ttrueb
   | ibvf : valueb tfalseb.

   Inductive stepb : forall {T : typ}, tmb T -> tmb T -> Prop :=
   | ST_IfTrueb : forall  T (t1  t2 : tmb T),
       stepb (tifb _ ttrueb t1 t2) t1
   | ST_IfFalseb : forall T (t1 t2 : tmb T),
       stepb (tifb _ tfalseb t1 t2) t2
    | ST_Ifb (T : typ): forall (t1 : tmb TBool) t1' (t2 t3 : tmb T),
       stepb t1 t1' -> stepb (tifb _ t1 t2 t3) (tifb _ t1' t2 t3)
   
   | ST_Succb : forall t1 t1',
       stepb t1 t1' -> stepb (tsuccb t1) (tsuccb t1')
   | ST_PredZerob : stepb (tpredb tzerob)  tzerob
   | ST_PredSuccb : forall t1,
       valueb t1 -> stepb (tpredb (tsuccb t1)) t1
   | ST_Predb : forall t1 t1',
       stepb t1 t1' -> stepb (tpredb t1) (tpredb t1')
   | ST_IszeroZerob : stepb (tiszerob tzerob)  ttrueb
   | ST_IszeroSuccb : forall t1,
        valueb t1 ->  stepb (tiszerob (tsuccb t1)) tfalseb
   | ST_Iszerob : forall t1 t1',
       stepb t1  t1' -> stepb (tiszerob t1) (tiszerob t1').
   
*)
