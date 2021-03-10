(* Quickchick implementation of the typed arithmetic language
from Software Foundations's Types.v chapter

Authors: Andrea Colò & Alberto Momigliano

*)
From QuickChick Require Import QuickChick.
Require Import Arith Bool List ZArith. 
(* Require Export ExtLib.Structures.Monads. *)
Export MonadNotation. 
Open Scope monad_scope.
Import QcNotation. (* Suppress some annoying warnings: *)
Set Warnings "-extraction-opaque-accessed,-extraction". 
  Require Import String. Local Open Scope string.


(* The language and its semantics, both functionally and relationally:*)

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tzero : tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tiszero : tm -> tm
  | tif : tm -> tm -> tm -> tm.

Inductive typ : Type :=
  |TBool : typ
  |TNat : typ.

Fixpoint isnumericval t :=
    match t with
         tzero => true
        | tsucc(t1) => isnumericval t1
        | _ => false
    end.

Definition isval t :=
    match t with
        | ttrue  => true
        | tfalse => true
        | t => if isnumericval t then true else false
    end.

Instance optionMonad : Monad option :=
  {
    ret T x :=
      Some x ;
    bind T U m f :=
      match m with
        None => None
      | Some x => f x
      end
  }.

Fixpoint eval1Monad t  :=
   match t with
      | tif ttrue t2 t3 => ret t2
      | tif tfalse t2 t3 => ret t3
      | tif t1 t2 t3 =>
           t1' <- eval1Monad t1 ;;
           ret (tif t1' t2 t3)
      |tsucc(t1) =>
           t1' <- eval1Monad t1 ;;
           ret (tsucc(t1'))
      |tpred  tzero => ret  tzero
      |tpred(tsucc(nv1)) =>
          if (isnumericval nv1) then ret nv1
          else
            t1' <- eval1Monad nv1 ;;
            ret (tpred(tsucc(t1')))
      |tpred(t1) =>
           t1' <- eval1Monad t1 ;;
           ret (tpred(t1'))
      |tiszero  tzero => ret ttrue
      |tiszero(tsucc(nv1)) =>
          if (isnumericval nv1) then ret tfalse
          else
           t1' <- eval1Monad nv1 ;;
           ret (tiszero(tsucc( t1')))
      | tiszero(t1)  =>
           t1' <- eval1Monad t1 ;;
           ret (tiszero( t1'))
      |_ =>  None
  end.

Definition canStep e :=
    match eval1Monad e with
    | Some _ => true
    | None => false
    end.

Definition eqTy t1 t2 :=
  match t1,t2 with
  |TBool,TBool => true
  |TNat,TNat => true
  |_,_ => false
  end.

Fixpoint typeof t :=
  match t with
  | ttrue => ret TBool
  | tfalse => ret TBool
  |  tzero => ret TNat
  | tsucc(t1) =>
      t' <- typeof t1 ;;
      if eqTy t' TNat then ret TNat
      else None
  | tpred(t1) =>
      t' <- typeof t1 ;;
      if eqTy t' TNat then ret TNat
      else None
  | tiszero(t1) =>
      t' <- typeof t1 ;;
      if eqTy t' TNat then ret TBool
      else None
  | tif t1 t2 t3 =>
      t' <- typeof t1 ;;
      if eqTy t' TBool then
        t' <- typeof t2 ;;
        t'' <- typeof t3 ;;
        if eqTy t' t'' then ret t'
        else None
      else None
  end.

Definition typeable e :=
    match typeof e with
    |Some _ => true
    |_ => false
    end.

Definition progressConclusion e :=
   isval e || canStep e.

Instance eq_dec_ty (y1 y2 :  typ) : Dec (y1 = y2).
Proof. dec_eq. Defined.

Definition preservation t tau :=
   match eval1Monad t with
   |None => true 
   |Some t' =>
     match typeof t' with
     |Some tt' => (tt' = tau)?
     |None => false
     end
    end.

Definition preservation2 t' tau :=
    match typeof t' with
    |Some tt' => (tt' = tau ?)
    |None => false
    end.

(*--------------------------------------------*)

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

Definition has_type1 tau t := has_type t tau.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : forall t, nvalue t -> nvalue (tsucc t).


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

Hint Constructors step : core.

(* QC:*)

Extract Constant defNumTests  => "500". 

Derive(Arbitrary,Show) for tm.

(*---------------------------------------------*)
(*! Section TEST_PROGRESS with ==> *)

Definition progressP1 e :=
   (typeable e) ==> (progressConclusion e).

(*! QuickCheck progressP1. *)
(*
QuickChecking progressP1
+++ Passed 500 tests (490 discards)
*)


(*---------------------------------------*)
(*! Section TEST_PROGRESS with custom generator for well typed terms *)

Derive (Arbitrary,Show) for typ.


Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200).


Fixpoint gen_term_size (n:nat) (t:typ) : G tm :=
  match n with
    | 0 =>
      match t with
      |TNat => returnGen  tzero
      |TBool => oneOf [returnGen ttrue; returnGen tfalse]
      end
    | S n' =>
        m <- choose (0, n');;
        match t with
        | TNat =>
          oneOf [returnGen  tzero;
                 liftGen tsucc (gen_term_size (n'-m) TNat) ;
                 liftGen tpred (gen_term_size (n'-m) TNat) ;
                 liftGen3 tif (gen_term_size (n'-m) TBool)
                               (gen_term_size (n'-m) TNat)
                               (gen_term_size (n'-m) TNat)]
        | TBool =>
          oneOf [returnGen ttrue; returnGen tfalse;
                liftGen tiszero (gen_term_size (n'-m) TNat);
                liftGen3 tif (gen_term_size (n'-m) TBool)
                               (gen_term_size (n'-m) TBool)
                               (gen_term_size (n'-m) TBool)]
        end
    end.

Definition gen_term (tau : typ) :=
  sized (fun s => gen_term_size s tau ).

Fixpoint term_size (t : tm) : nat :=
  match t with
    | ttrue | tfalse |  tzero => 0
    | tsucc t' | tpred t' | tiszero t' =>
      1 + (term_size t')
    | tif t1 t2 t3 =>
      1 + (term_size t1 + term_size t2 + term_size t3)
  end.

Definition progressP2Collect :=
   forAll arbitrary (
               fun tau =>
                forAll (gen_term tau)
                (fun t =>
                  (collect (append "size " (show (term_size t)))
                (progressConclusion t)))).

(*! QuickCheck progressP2Collect. *)

(*
QuickChecking progressP2Collect
249 : "size 0"
128 : "size 1"
71 : "size 2"
26 : "size 3"
10 : "size 4"
8 : "size 5"
3 : "size 6"
2 : "size 7"
1 : "size 8"
1 : "size 14"
1 : "size 10"
+++ Passed 500 tests (0 discards)
*)

(*---------------------------------------*)
(*! Section TEST_PROGRESS with automatic derivation
of well typed terms   *)

Derive ArbitrarySizedSuchThat for (fun t => has_type t tau).
(*GenSizedSuchThathas_type*)

Definition progressST :=
  forAll arbitrary (fun tau : typ =>
                       forAll (genST (fun t => has_type t tau))
                              (fun mt =>
                                 match mt with
                                 | Some t => progressConclusion  t
                                 | None => false
                                 end)).
(*! QuickCheck progressST. *)
(* QuickChecking progressST
+++ Passed 500 tests (0 discards)
*)

(*! Section TEST_PRESERVATION_ST *)

Instance eq_dec_option_tm (y1 y2 : option tm) : Dec (y1 = y2).
Proof. dec_eq. Defined.

Instance eq_dec_option_tp (y1 y2 : option typ) : Dec (y1 = y2).
Proof. dec_eq. Defined.


Definition canStepOption (t:option tm) : (bool * (option tm)):=
  match t with 
  |Some t => 
      match eval1Monad t with
      |Some t' => (true,Some t')
      |None => (false,None)
      end
  |None => (false,None)
  end.


Definition preservationST :=
  forAll arbitrary (fun tau : typ =>
                     forAll (genST (fun t => has_type t tau))
                            (fun mt =>
                              ((fst (canStepOption mt)) = true ?)==>

                              match canStepOption mt with
                              |(true, Some t')=>
                                 preservation2 t' tau
                              |_ => true
                              end
                            )).

(*! QuickCheck preservationST. *)
(* QuickChecking preservationST
+++ Passed 500 tests (424 discards) *)

Definition preservationSTs :=
  forAll arbitrary (fun tau : typ =>
                     forAll (genST (fun t => has_type t tau))
                            (fun mt =>
                              match canStepOption mt with
                              |(true, Some t')=>
                                 preservation2 t' tau
                              |_ => true
                              end
                            )).

(* QuickCheck preservationSTs. *)

(*! Section TEST_PRESERVATION_SUCHTHATMAYBE *)

Definition wellTypedTermThatCanStepGen T :  G (option tm) :=
  suchThatMaybe (gen_term T) canStep.

Definition someOrNone (t:option tm) :=
  match t with
  |None => "None"
  |Some _ => "Some _"
  end.


Definition preservationP2Collect :=
   forAll arbitrary (
               fun tau =>
                 forAll (wellTypedTermThatCanStepGen tau)
                 (fun t =>
                    collect (someOrNone t) (

                    match t with
                    |None => true
                    |Some t' => preservation t' tau
                    end
                    )
                 )).
(*! QuickChick preservationP2Collect. *)
(*QuickChecking preservationP2Collect
391 : "Some _"
109 : "None"
+++ Passed 500 tests (0 discards)*)


(*! Section TEST_SUBJECT_EXPANSION *)
(*t --> t' and ⊢ t' ∈ T ,then ⊢ t ∈ T*)

Definition subject_expansion t :=
  match eval1Monad t with
  |None => true (*does not happen if t canStep*)
  |Some t' =>
    let T := typeof t' in
     match T with
     |Some _ => (T = typeof t)?
     |None => true (*since the hypothesis that t'is typeable
                     is false, than the property is true*)
     end
  end.

(*----SUBJECT_EXPANSION SUCHTHATMAYBE----*)
Definition canStepAndResultIsTypeable e :=
    match eval1Monad e with
    | Some e' => typeable e'
    | None => false
    end.

Definition termsThatCanStepAndResultIsTypeable : G (option tm) :=
  suchThatMaybe arbitrary canStepAndResultIsTypeable.

Definition subject_expansionP1 :=
    forAllShrink  (termsThatCanStepAndResultIsTypeable)
      shrink
     (fun t =>
        collect (someOrNone t) (
        (t <> None)? ==>
        match t with
        |None => true
        |Some t' =>
          subject_expansion t'
        end
        )
     ).
(*! QuickCheck subject_expansionP1.*)
(*QuickChecking subject_expansionP1
Some tif tfalse (tiszero tzero) tzero
20 : (Discarded) "None"
2 : "Some _"
*** Failed after 3 tests and 3 shrinks. (20 discards)
*)

(*----SUBJECT_EXPANSION_Derive ArbitrarySizedSuchThat----*)
Instance dec_nvalue t : Dec (nvalue t).
Proof.
dec_eq.
induction t; 
try solve[right => contra; inversion contra].
- left; constructor.
- destruct IHt as [L | R]; [left; constructor | right => contra; inversion contra]; eauto.
Defined.

Derive ArbitrarySizedSuchThat for (fun t1 : tm => nvalue t1).

Derive ArbitrarySizedSuchThat for (fun t => step t t1).

(* NO SHRINK *)
Definition subject_expansionP  :=
  forAll arbitrary  (fun t1 : tm =>
      forAll (genST (fun t => step t t1))(
          fun t' => 
               match t' with
               |Some t'' => subject_expansion t''
               |_ => true 
               end
       )).
(*! QuickCheck subject_expansionP. *)
(* QuickChecking subject_expansionP
tzero
Some tif tfalse (tif (tiszero (tiszero tfalse)) (tif (tif ttrue (tpred ttrue) (tsucc ttrue)) (tsucc ttrue) tfalse) (tiszero ttrue)) tzero
*** Failed after 5 tests and 0 shrinks. (0 discards)
 *)





