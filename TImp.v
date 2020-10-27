(** * TImp: Case Study: a Typed Imperative Language

ported to pure relational by am 

to be finished: makes little sense as properties are concerned: should be small step*)

Require Import Bool Arith EqNat List. Import ListNotations.


(** FULL: ** Identifiers *)

(** For the type of identifiers of TImp we will use a wrapper around 
    plain natural numbers. *)

Inductive id :=
|  Id : nat -> id.


(** ** Types *)

(** Here is the type of TImp types: *)

Inductive ty := TBool | TNat. 


(** ** List-Based Maps *)

Definition Map A := list (id * A).

(** The [empty] map is the empty list. *)

Definition map_empty {A} : Map A := [].

(** TERSE: *** *)

(** To [get] the binding of an identifier [x], we just need to walk 
    through the list and find the first [cons] cell where the key 
    is equal to [x], if any. 

Fixpoint map_get {A} (m : Map A) x : option A :=
  match m with
  | [] => None
  | (k, v) :: m' => if x = k ? then Some v else map_get m' x
  end.
*)
(** TERSE: *** *)

(** To [set] the binding of an identifier, we just need to [cons] 
    it at the front of the list. *) 

Definition map_set {A} (m:Map A) (x:id) (v:A) : Map A := (x, v) :: m.

(** TERSE: *** *)

(** Finally, the domain of a map is just the set of its keys. *)
Fixpoint map_dom {A} (m:Map A) : list id :=
  match m with
  | [] => []
  | (k', v) :: m' => k' :: map_dom m'
  end.

(** TERSE: *** *)
(** We next introduce a simple inductive relation, [bound_to m x a], that 
    holds precisely when the binding of some identifier [x] is equal to [a] in 
    [m] *)
(*
Inductive bound_to {A} : Map A -> id -> A -> Prop :=
  | Bind : forall x m a, map_get m x = Some a -> bound_to m x a.
*)
  
(** ** Contexts *)

(** Typing contexts in TImp are just maps from identifiers to types. *)

Definition context := Map ty.


(** * Expressions *)

(** We are now ready to introduce the syntax of expressions in TImp.
    The original Imp had two distinct types of expressions,
    arithmetic and boolean expressions; variables were only
    allowed to range over natural numbers. In TImp, we extend
    variables to range over boolean values as well, and we collapse
    expressions into a single type [exp]. *)

Inductive exp : Type :=
  | EVar : id -> exp
  | ENum : nat -> exp
  | EPlus : exp -> exp -> exp
  | EMinus : exp -> exp -> exp
  | EMult : exp -> exp -> exp
  | ETrue : exp
  | EFalse : exp
  | EEq : exp -> exp -> exp
  | ELe : exp -> exp -> exp
  | ENot : exp -> exp
  | EAnd : exp -> exp -> exp.


(** ** Typed Expressions *)

(** FULL: The following inductive relation characterizes well-typed
    expressions of a particular type. It is straightforward, using
    [bound_to] to access the typing context in the variable case *)

Print In.

Inductive mem  {A : Type} (a : A):  list A -> Prop :=
|m1: forall l, mem a (a :: l)
|m2 : forall b l,mem a l -> mem a (b :: l).
 
Reserved Notation "Gamma '||-' e '\IN' T" (at level 40).

Inductive has_type : context -> exp -> ty -> Prop := 
| Ty_Var : forall x T Gamma, 
    mem (x, T) Gamma -> Gamma ||- EVar x \IN T
| Ty_Num : forall Gamma n, 
    Gamma ||- ENum n \IN TNat
| Ty_Plus : forall Gamma e1 e2, 
    Gamma ||- e1 \IN TNat -> Gamma ||- e2 \IN TNat ->
    Gamma ||- EPlus e1 e2 \IN TNat                                    
| Ty_Minus : forall Gamma e1 e2, 
    Gamma ||- e1 \IN TNat -> Gamma ||- e2 \IN TNat ->
    Gamma ||- EMinus e1 e2 \IN TNat                                    
| Ty_Mult : forall Gamma e1 e2, 
    Gamma ||- e1 \IN TNat -> Gamma ||- e2 \IN TNat ->
    Gamma ||- EMult e1 e2 \IN TNat                                    
| Ty_True : forall Gamma, Gamma ||- ETrue \IN TBool
| Ty_False : forall Gamma, Gamma ||- EFalse \IN TBool
| Ty_Eq : forall Gamma e1 e2, 
    Gamma ||- e1 \IN TNat -> Gamma ||- e2 \IN TNat ->
    Gamma ||- EEq e1 e2 \IN TBool
| Ty_Le : forall Gamma e1 e2, 
    Gamma ||- e1 \IN TNat -> Gamma ||- e2 \IN TNat ->
    Gamma ||- ELe e1 e2 \IN TBool
| Ty_Not : forall Gamma e, 
    Gamma ||- e \IN TBool ->  Gamma ||- ENot e \IN TBool
| Ty_And : forall Gamma e1 e2, 
    Gamma ||- e1 \IN TBool -> Gamma ||- e2 \IN TBool ->
    Gamma ||- EAnd e1 e2 \IN TBool

where "Gamma '||-' e '\IN' T" := (has_type Gamma e T).

(** While the typing relation is almost entirely standard, there is a 
    choice to make about the [Ty_Eq] rule. The [Ty_Eq] constructor
    above requires that the arguments to an equality check are both 
    arithmetic expressions (just like it was in Imp), which simplifies
    some of the discussion in the remainder of the chapter. We could
    have allowed for equality checks between booleans as well - that will
    become an exercise at the end of this chapter. *)

(** FULL: ** Values *)

(** In the original Imp language from _Logical Foundations_, variables
    ranged over natural numbers, so states were just maps from
    identifiers to [nat].  Since we now want to extend this to also
    include booleans, we need a type of [value]s that includes
    both. *)

Inductive value := VNat : nat -> value | VBool : bool -> value.



(** TERSE: *** *)
(** We can also quickly define a typing relation for values, a Dec instance
    for it, and a generator for values of a given type. *)
  
Inductive has_type_value : value -> ty -> Prop :=
  | TyVNat  : forall n, has_type_value (VNat  n) TNat
  | TyVBool : forall b, has_type_value (VBool b) TBool.

(** FULL: ** States *)
(** TERSE: *** *)

(** _States_ in TImp are just maps from identifiers to values *)

Definition state := Map value.

(** We introduce an inductive relation that specifies when a state is
    well typed in a context (that is, when all of its variables are
    mapped to values of appropriate types).
  
    We encode this in an element-by-element style inductive relation:
    empty states are only well typed with respect to an empty context,
    while non-empty states need to map their head identifier to a value of
    the appropriate type (and their tail must similarly be well
    typed). *)

Inductive well_typed_state : context -> state -> Prop :=
| TS_Empty : well_typed_state map_empty map_empty
| TS_Elem  : forall x v T st Gamma, 
    has_type_value v T -> well_typed_state Gamma st ->
    well_typed_state ((x,T)::Gamma) ((x,v)::st).

(** * Evaluation *)

(** The evaluation function takes a state and an expression and
    returns an optional value, which can be [None] if the expression
    encounters a dynamic type error like trying to perform addition on
    a boolean. *)

Inductive plus : nat -> nat -> nat -> Prop :=
|pz n: plus O n n
|ps n m k  : plus n m k -> plus ( n + 1) m ( k + 1).

Inductive times : nat -> nat -> nat -> Prop :=
|tz n: times O n O
|ts n m k v : times n m k -> plus n k v -> times ( n + 1) m v.

Inductive eval (st : state) : exp ->  value -> Prop :=
  
  | evv x v: mem (x,v) st -> eval st (EVar x) v 
  | evn n: eval st (ENum n) (VNat n)
  | evp e1 e2 v1 v2 v: eval st e1 (VNat v1) -> eval st e2 (VNat v2) -> plus v1 v2 v 
    -> eval st (EPlus e1 e2) (VNat v)
    | evm e1 e2 v1 v2 v: eval st e1 (VNat v1) -> eval st e2 (VNat v2) -> plus v2 v1 v 
    -> eval st (EMinus e1 e2) (VNat v1)
| evmu e1 e2 v1 v2 v: eval st e1 (VNat v1) -> eval st e2 (VNat v2) -> times v1 v2 v 
    -> eval st (EMult e1 e2) (VNat v)
  |evt: eval  st ETrue   (VBool true  )
  | evf: eval st EFalse      (VBool false )
  | eveq e1 e2 n1: 
    eval st e1 (VNat n1)  -> eval st e2 (VNat n1) -> eval st (EEq e1 e2) (VBool true)
    (*add false and finish*)
    | E_Le:
      forall (a1 a2 : exp) (n1 n2 : nat),
        eval st a1 (VNat n1) ->
        eval st a2 (VNat n2) ->
        eval st (ELe a1 a2) (VBool (leb n1 n2))
  | E_Not:
      forall (b : exp) (b' : bool),
        eval st b (VBool b') ->
        eval st (ENot b) (VBool (negb b'))
  | E_And:
      forall (a b : exp) (a' b' : bool),
        eval st a (VBool a') ->
        eval st b (VBool b') ->
        eval st (EAnd a b) (VBool (andb a' b')).
        
        (*
  | ELe e1 e2 => 
    match eval st e1, eval st e2 with 
    | Some (VNat n1), Some (VNat n2) => Some (VBool (n1 <? n2))
    | _, _ => None
    end
  | ENot e => 
    match eval st e with 
    | Some (VBool b) => Some (VBool (negb b))
    | _ => None
    end
  | EAnd e1 e2  => 
    match eval st e1, eval st e2 with 
(* Let's include a silly bug here! *)
    | Some (VBool b), Some (VNat n2) => Some (VBool (negb b))
(*  | Some (VBool b1), Some (VBool b2) => Some (VBool (andb b1 b2)) *)
    | _, _ => None
    .
*)
(** TERSE: *** *)
(** _Type soundness_ states that, if we have an expression [e] of a
    given type [T] as well as a well-typed state [st], then evaluating
    [e] in [st] will never fail.*)


(* SOONER: Coq 8.8 supports nicer notation for tests like "isNone" *)
Conjecture expression_soundness : forall Gamma st e T,  
    well_typed_state Gamma st ->  Gamma ||- e \IN T ->
    exists v, eval st e v.

(** To test this property, we construct an appropriate checker: *)

(** TERSE: *** *)

(* QuickChick expression_soundness_exec. *)
(** 
<<
     ===>
       QuickChecking expression_soundness_exec
       [(1,TNat), (2,TNat), (3,TBool), (4,TNat)]
       [(1,VNat 0), (2,VNat 0), (3,VBool true), (4,VNat 0)]
       TBool
       Some EAnd (EAnd (EEq (EVar 4) (EVar 1)) (EEq (ENum 0) (EVar 4))) EFalse
       *** Failed after 8 tests and 0 shrinks. (0 discards)
>>
*)
(** Where is the bug??  Looks like we need some shrinking! *)

(** ** Shrinking for Expressions *)


(** TERSE: *** *)
(* QuickChick expression_soundness_exec'. *)
(** 
<<
     ===>
        QuickChecking expression_soundness_exec'
        [(1,TNat), (2,TNat), (3,TNat), (4,TBool)]
        [(1,VNat 0), (2,VNat 0), (3,VNat 0), (4,VBool false)]
        TBool
        Some EAnd ETrue ETrue
        *** Failed after 8 tests and 1 shrinks. (0 discards)
>>
*)

(** * Well-Typed Programs *)

(** Now we're ready to introduce TImp commands; they are just like the
    ones in Imp. *)

Inductive com : Type :=
  | CSkip  : com
  | CAss   : id  -> exp -> com
  | CSeq   : com -> com -> com
  | CIf    : exp -> com -> com -> com
  | CWhile : exp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).


(** We can now define what it means for a command to be well typed
    for a given context. The interesting cases are [TAss] and [TIf]/[TWhile]. 
    The first one, ensures that the type of the variable we are 
    assigning to is the same as that of the expression. The latter,
    requires that the conditional is indeed a boolean expression.
 *)

Inductive well_typed_com : context -> com -> Prop :=
  | TSkip : forall Gamma, well_typed_com Gamma CSkip
  | TAss  : forall Gamma x e T, 
      mem (x, T) Gamma -> 
      Gamma ||- e \IN T ->
      well_typed_com Gamma (CAss x e)
  | TSeq  : forall Gamma c1 c2, 
      well_typed_com Gamma c1 -> well_typed_com Gamma c2 ->
      well_typed_com Gamma (CSeq c1 c2)
  | TIf : forall Gamma b c1 c2, 
      Gamma ||- b \IN TBool ->
      well_typed_com Gamma c1 -> well_typed_com Gamma c2 ->
      well_typed_com Gamma (CIf b c1 c2)
  | TWhile : forall Gamma b c,
      Gamma ||- b \IN TBool -> well_typed_com Gamma c -> 
      well_typed_com Gamma (CWhile b c).

(* TERSE: HIDEFROMHTML *)
Lemma has_type_deterministic Gamma e (T1 T2 : ty) : 
  has_type e Gamma T1 -> has_type e Gamma T2 -> 
  T1 = T2.
(* FOLD *)
Proof.
  destruct T1; destruct T2; intros H1 H2; eauto;
    inversion H1; inversion H2; subst; eauto; try congruence;
  inversion H7; subst;
    eapply bind_deterministic; eauto.
Qed.
(* /FOLD *)
(* FULL *)
(** TERSE: *** *)
(** To complete the tour of testing for TImp, here is a (buggy??)
    evaluation function for commands given a state. To ensure
    termination, we've included a "fuel" parameter: if it gets to zero
    we return [OutOfGas], signifying that we're not sure if evaluation
    would have succeeded, failed, or diverged if we'd gone on
    evaluating. *)
  
Inductive result := 
| Success : state -> result
| Fail : result 
| OutOfGas : result. 

(* SOONER: This would look much nicer in monadic syntax... *)
Fixpoint ceval (fuel : nat) (st : state) (c : com) : result :=
  match fuel with 
  | O => OutOfGas
  | S fuel' => 
    match c with
    | SKIP =>
        Success st
    | x ::= e =>
        match eval st e with 
        | Some v => Success (map_set st x v)
        | _ => Fail 
        end
    | c1 ;;; c2 =>
        match ceval fuel' st c1 with 
        | Success st' =>  ceval fuel' st' c2 
        | _ => Fail 
(* HIDE *)
(* Bug : On OutOfGas should out of Gas :
        | r => r
        *)
(* /HIDE *)
        end
    | TEST b THEN c1 ELSE c2 FI =>
      match eval st b with 
      | Some (VBool b) =>
        ceval fuel' st (if b then c1 else c2)
      | _ => Fail
      end
    | WHILE b DO c END =>
      match eval st b with 
      | Some (VBool b') =>
        if b' 
          then ceval fuel' st (c ;;; WHILE b DO c END) 
          else Success st
      | _ => Fail
      end
    end
  end.

Definition isFail r := 
  match r with 
  | Fail => true
  | _ => false
  end.

(** TERSE: *** *)

(** _Type soundness_: well-typed commands never fail. *)

Conjecture well_typed_state_never_stuck : 
  forall Gamma st, well_typed_state Gamma st ->
  forall c, well_typed_com Gamma c ->
  forall fuel, isFail (ceval fuel st c) = false.

(** TERSE: *** *)
(* EX4M (well_typed_state_never_stuck) *)
(** Write a checker for the above property, find any bugs, and fix them. *)

(* SOLUTION *)
Definition well_typed_state_never_stuck_exec := 
  let num_vars := 4 in 
  let top_level_size := 5 in
  forAll (gen_context num_vars)  (fun Gamma =>
  forAll (gen_well_typed_state Gamma) (fun st =>
  forAllShrink arbitrary shrink (fun fuel =>
  forAllShrink (gen_com_typed_sized 3 Gamma) 
               (lift_shrink (shrink_com_typed Gamma)) 
               (fun mc => 
  match mc with 
  | Some c => negb (isFail (ceval fuel st c))
  | _ => true
  end)))).    

(* SOONER: So... is the property correct, or not?? *)
(* SOONER: No, there is a bug inside "HIDE" in th definition. *)
(* SOONER: Is this still a sooner? *)
(* /SOLUTION *)

(* EX4M (ty_eq_polymorphic) *)
(** In the [has_type] relation we allowed equality checks between 
    only arithmetic expressions. Introduce an additional typing 
    rule that allows for equality checks between booleans.
[[
    | Ty_Eq : forall Gamma e1 e2, 
        Gamma ||- e1 \IN TBool -> Gamma ||- e2 \IN TBool ->
        Gamma ||- EEq e1 e2 \IN TBool
]]
   Make sure you also update the evaluation relation to 
   compare boolean values. Update the generators and shrinkers
   accordingly to find counterexamples to the buggy properties
   above. 

   HINT: When updating the shrinker, you will need to 
   come up with the type of the equated expressions. The 
   [Dec] instance of [has_type] will come in handy.
*)
   
