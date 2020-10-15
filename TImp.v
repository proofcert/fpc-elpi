(** * TImp: Case Study: a Typed Imperative Language

ported to pure relational by am *)

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
    is equal to [x], if any. *)

Fixpoint map_get {A} (m : Map A) x : option A :=
  match m with
  | [] => None
  | (k, v) :: m' => if x = k ? then Some v else map_get m' x
  end.

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

Inductive bound_to {A} : Map A -> id -> A -> Prop :=
  | Bind : forall x m a, map_get m x = Some a -> bound_to m x a.

  
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

Reserved Notation "Gamma '||-' e '\IN' T" (at level 40).

(* SOONER: The notation here is hideous. Remove.  BCP (later):
   actually, I'm not sure I hate it all that much now...*)
(* SOONER: LEO: We can't use |- (because it's used in 'match goal
   with') so I'm almost ok with ||-. I really don't like the \IN... *)
Inductive has_type : context -> exp -> ty -> Prop := 
| Ty_Var : forall x T Gamma, 
    bound_to Gamma x T -> Gamma ||- EVar x \IN T
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


(** TERSE: *** *)
(* FULL *)
(** Once again, we need a decidable instance for the typing relation of
    TImp. You can skip to the next exercise if you are not interested in
    specific proof details. *)
(* LATER: _Should_ people be interested in this?  When would they
   need it? *)
(* LATER: Just like before, this is something we need to address 
   at some point. [Dec] requires proofs, which is annoying. We could 
   change everything to use [DecOpt] (or whatever we rename that to,
   but that is after the summer school... *)

(* /FULL *)
(* TERSE: HIDEFROMHTML *)
(** We will need a bit more automation for this proof. We will
    have a lot of hypotheses of the form: 
[[
   IH : forall (T : ty) (Gamma : context),
          ssrbool.decidable (Gamma ||- e1 \IN T)
]]
 
    Using a brute-force approach, we instantiate such [IH]
    with both [TNat] and [TBool], destruct them and then 
    call [solve_sum]. 
     
    The [pose proof] tactic introduces a new hypothesis 
    in our context, while [clear IH] removes it so that 
    we don't try the same instantiations again and 
    again.
*)

Ltac solve_inductives Gamma :=
  repeat (match goal with 
      [ IH : forall _ _, _ |- _ ] =>
      let H1 := fresh "H1" in 
      pose proof (IH TNat Gamma) as H1;
      let H2 := fresh "H2" in 
      pose proof (IH TBool Gamma) as H2;
      clear IH;
      destruct H1; destruct H2; solve_sum
    end).
(* TERSE: /HIDEFROMHTML *)

(** Typing in TImp is decidable: given an expression [e], a context [Gamma] 
    and a type [T], we can decide whether [has_type Gamma e T] holds. *)

Instance dec_has_type (e : exp) (Gamma : context) (T : ty) 
  : Dec (Gamma ||- e \IN T).
(* FOLD *)
Proof with solve_sum.
(* HIDE: I need move: :'( *)
  constructor.
  generalize dependent Gamma.
  generalize dependent T.
  induction e; intros T Gamma; unfold ssrbool.decidable;
    try solve [destruct T; solve_sum];
    try solve [destruct T; solve_inductives Gamma].
  (* bound_to case: *)
  destruct (dec_bound_to Gamma i T); destruct dec; solve_sum.
Defined.
(* /FOLD *)

(* FULL *)
(* EX3M (arbitraryExp) *)
(** Derive [Arbitrary] for expressions.  To see how good it is at
    generating _well-typed_ expressions, write a conditional property 
    [cond_prop] that is (trivially) always true, with the precondition 
    that some expression is well-typed. Try to check that property like 
    this:
[[
    QuickChickWith (updMaxSize stdArgs 3) cond_prop.
]]
    This idiom sets the maximum-size parameter for all generators to
    [3], rather the default, which is something larger like 10.  When
    generating examples, QuickChick will start with size 0, gradually
    increase the size until the maximum size is reached, and then
    start over.  What happens when you vary the size bound? *)

(* SOLUTION *)
Derive Arbitrary for exp.

Definition cond_prop (Gamma : context) (e : exp) (t : ty) := 
  (has_type Gamma e t)? ==> true.

(* QuickChickWith (updMaxSize stdArgs 3) cond_prop. *)
(* /SOLUTION *)
(** [] *)
(* /FULL *)

(** ** Generating Typed Expressions *)

(* SOONER: We need to add this experiment. Bad generation + filtering. *)
(** Instead of generating expressions and filtering them using
    [has_type], we can be smarter and generate _well-typed_
    expressions for a given context directly.

    It is common for conditional generators to return [option]s,
    allowing the possibility of failure if a wrong choice is made
    internally. For example, if we wanted to generate an expression of
    type [TNat] and chose to try to do so by generating a variable,
    then we might not be able to finish (if the context is empty or
    only binds booleans). *)

(** To chain together two generators with types of the form 
    [G (option ...)], we need to execute the first generator, match 
    on its result, and, when it is a [Some], apply the second generator. *)

Definition bindGenOpt {A B : Type} 
             (gma : G (option A)) (k : A -> G (option B))
           : G (option B) :=
  ma <- gma ;;
  match ma with 
  | Some a => k a 
  | None => ret None
  end.

(** TERSE: *** *)
(** This pattern is common enough that QuickChick introduces explicit monadic 
    notations. *)
(* SOONER: Is GOpt a monad "in two ways"?  How do we prevent confusion
   between them? *)
(* SOONER: Typeclass priorities... Mention that explicitly.*)

Print GOpt.
(** <<
    GOpt = fun A : Type => G (option A)
         : Type -> Type
>> 
*)

Check Monad_GOpt. 
(** <<
    Monad_GOpt
         : Monad GOpt
>>
*)

(** TERSE: *** *)

(** This brings us to our first interesting generator -- one for typed
    expressions.  We assume that [Gamma] and [T] are inputs to the
    generation process.  We also use a [size] parameter to control the
    depth of generated expressions (i.e., we'll define a sized
    generator). *)

(** Let's start with a much smaller relation: [has_type_1] (which
    consists of just the first constructor of [has_type]), to
    demonstrate how to build up complex generators for typed
    expressions from smaller parts. *)

Module TypePlayground1.

Inductive has_type : context -> exp -> ty -> Prop := 
  | Ty_Var : forall x T Gamma, 
      bound_to Gamma x T -> has_type Gamma (EVar x) T.

End TypePlayground1.

(** To generate [e] such that [has_type Gamma e T] holds, we need to
    pick one of its constructors (there is only one choice, here) and
    then try to satisfy its preconditions by generating more things.
    To satisfy [Ty_Var] (given [Gamma] and [T]), we need to generate
    [x] such that [bound_to Gamma x T]. But we already have such a
    generator!  We just need to wrap it in an [EVar].  *)

Definition gen_typed_evar (Gamma : context) (T : ty) : GOpt exp :=
  x <- gen_typed_id_from_context Gamma T;;
  ret (EVar x).

(** (Note that this is the [ret] of the [GOpt] monad.) *)

(** TERSE: *** *)
(** Now let's consider an extended typing relation, extending the 
    previous one with all of the constructors of [has_type] that do
    not recursively require [has_type] as a side-condition. These will
    be the _base cases_ for our final generator. *)

Module TypePlayground2.

Inductive has_type : context -> exp -> ty -> Prop :=
| Ty_Var : forall x T Gamma, 
    bound_to Gamma x T -> has_type Gamma (EVar x) T
| Ty_Num : forall Gamma n, 
    has_type Gamma  (ENum n) TNat
| Ty_True : forall Gamma, has_type Gamma ETrue TBool
| Ty_False : forall Gamma, has_type Gamma EFalse TBool.

End TypePlayground2.

(** We can already generate values satisfying [Ty_Var] using
    [gen_typed_evar].  For the rest of the rules, we will need to
    pattern match on the input [T], since [Ty_Num] can only be used if
    [T = TNat], while [Ty_True] and [Ty_False] can only be used if [T
    = TBool].  *)

Definition base' Gamma T : list (GOpt exp) := 
      gen_typed_evar Gamma T ::
      match T with 
      | TNat  => [ n <- arbitrary;; ret (Some (ENum n))]
      | TBool => [ ret ETrue ; ret EFalse ]
      end.

(** TERSE: *** *)

(** We now need to go from a list of (optional) generators to a 
    single generator. We could do that using the [oneOf] combinator (which
    chooses uniformly), or the [freq] combinator (by adding weights).

    Instead, we introduce a new one, called [backtrack]:
[[
       backtrack : list (nat * GOpt ?A) -> GOpt ?A
]]
*)

(** Just like [freq], [backtrack] selects one of the generators
    according to the input weights. Unlike [freq], if the chosen
    generator fails (i.e. produces [None]), [backtrack] will discard
    it, choose another, and keep going until one succeeds or all
    possibilities are exhausted. Our base-case generator could then be
    like this: *)
    
Definition base Gamma T := 
      (2, gen_typed_evar Gamma T) ::
      match T with 
      | TNat  => [ (2, n <- arbitrary;; ret (Some (ENum n)))]
      | TBool => [ (1, ret ETrue)
                 ; (1, ret EFalse) ]
      end.

Definition gen_has_type_2 Gamma T := backtrack (base Gamma T).

(** TERSE: *** *)
(** To see how we handle recursive rules, let's consider a third
    sub-relation, [has_type_3], with just variables and addition: *)

Module TypePlayground3.
  
Inductive has_type : context -> exp -> ty -> Prop :=
 | Ty_Var : forall x T Gamma, 
     bound_to Gamma x T -> has_type Gamma (EVar x) T
 | Ty_Plus : forall Gamma e1 e2, 
    has_type Gamma e1 TNat -> has_type Gamma e2 TNat ->
    has_type Gamma (EPlus e1 e2) TNat.

End TypePlayground3.

(** Typing derivations involving [EPlus] nodes are binary trees, so we
    need to add a [size] parameter to enforce termination. The base
    case ([Ty_Var3]) is handled using [gen_typed_evar] just like
    before.  The non-base case can choose between trying to generate
    [Ty_Var3] and trying to generate [Ty_Plus3]. For the latter, the
    input type [T] must be [TNat], otherwise it is not
    applicable. Once again, this leads to a match on [T]: *)

Fixpoint gen_has_type_3 size Gamma T : GOpt exp := 
  match size with 
  | O => gen_typed_evar Gamma T
  | S size' => 
    backtrack 
      ([ (1, gen_typed_evar Gamma T) ] 
      ++ match T with 
         | TNat => 
           [ (size, e1 <- gen_has_type_3 size' Gamma TNat;;
                    e2 <- gen_has_type_3 size' Gamma TNat;;
                    ret (EPlus e1 e2)) ]
         | _ => []
         end)
  end.

(** TERSE: *** *)
(** Putting all this together, we get the full generator for
    well-typed expressions. *)

Fixpoint gen_exp_typed_sized
            (size : nat) (Gamma : context) (T : ty) 
       : GOpt exp :=
  let base := base Gamma T in
  let recs size' := 
    match T with 
    | TNat =>
      [ (size, e1 <- gen_exp_typed_sized size' Gamma TNat ;; 
            e2 <- gen_exp_typed_sized size' Gamma TNat ;; 
            ret (EPlus e1 e2)) 
      ; (size, e1 <- gen_exp_typed_sized size' Gamma TNat ;; 
            e2 <- gen_exp_typed_sized size' Gamma TNat ;; 
            ret (EMinus e1 e2)) 
      ; (size, e1 <- gen_exp_typed_sized size' Gamma TNat ;; 
            e2 <- gen_exp_typed_sized size' Gamma TNat ;; 
            ret (EMult e1 e2)) ]
    | TBool => 
    [ (size, e1 <- gen_exp_typed_sized size' Gamma TNat ;; 
             e2 <- gen_exp_typed_sized size' Gamma TNat ;; 
             ret (EEq e1 e2)) 
       ; (size, e1 <- gen_exp_typed_sized size' Gamma TNat ;; 
             e2 <- gen_exp_typed_sized size' Gamma TNat ;; 
             ret (ELe e1 e2)) 
       ; (size, e1 <- gen_exp_typed_sized size' Gamma TBool ;; 
             ret (ENot e1))
       ; (size, e1 <- gen_exp_typed_sized size' Gamma TBool ;; 
             e2 <- gen_exp_typed_sized size' Gamma TBool ;; 
             ret (EAnd e1 e2)) ]
    end in
  match size with 
  | O => 
    backtrack base 
  | S size' => 
    backtrack (base ++ recs size')
  end.

(** TERSE: *** *)

(** When writing such complex generators, it's good to have some tests
    to verify that we are generating what we expect. For example, here
    we would expect [gen_exp_typed_sized] to always return expressions
    that are well typed.
    
    We can use [forAll] to encode such a property. *)

(* SOONER: Explain: Why does gen_typed_has_typed return false? *)
Definition gen_typed_has_type :=
  let num_vars := 4 in
  let top_level_size := 3 in 
  forAll (gen_context num_vars) (fun Gamma =>
  forAll arbitrary (fun T =>                                   
  forAll (gen_exp_typed_sized top_level_size Gamma T) (fun me =>
  match me with 
  | Some e => (has_type Gamma e T)?
  | None => false 
  end))).
(* HIDE: @LEO I really want some existential Dec stuff... *)
(* HIDE: I do too. But I want to redo all of the typeclass infrastructure :) *)

(* QuickChick gen_typed_has_type. *)

(** * Values and States *)

(** FULL: ** Values *)

(** In the original Imp language from _Logical Foundations_, variables
    ranged over natural numbers, so states were just maps from
    identifiers to [nat].  Since we now want to extend this to also
    include booleans, we need a type of [value]s that includes
    both. *)

Inductive value := VNat : nat -> value | VBool : bool -> value.

Derive Show for value.

(** TERSE: *** *)
(** We can also quickly define a typing relation for values, a Dec instance
    for it, and a generator for values of a given type. *)
  
Inductive has_type_value : value -> ty -> Prop :=
  | TyVNat  : forall n, has_type_value (VNat  n) TNat
  | TyVBool : forall b, has_type_value (VBool b) TBool.

Instance dec_has_type_value v T : Dec (has_type_value v T).
(* FOLD *)
Proof. constructor; unfold ssrbool.decidable.
destruct v; destruct T; solve_sum.
Defined.
(* /FOLD *)

Definition gen_typed_value (T : ty) : G value :=
  match T with 
  | TNat  => n <- arbitrary;; ret (VNat n)
  | TBool => b <- arbitrary;; ret (VBool b)
  end.

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

Instance dec_well_typed_state Gamma st : Dec (well_typed_state Gamma st).
(* FOLD *)
Proof. 
constructor; unfold ssrbool.decidable.
generalize dependent Gamma.
induction st; intros; destruct Gamma; solve_sum.
destruct a as [a v]; destruct p as [a' T].
destruct (@dec (a = a') _ ); solve_sum.
subst; specialize (IHst Gamma); destruct IHst; solve_sum.
destruct (dec_has_type_value v T); destruct dec; solve_sum.
Defined.
(* /FOLD *)

(** TERSE: *** *)
(* LATER: Check whether we can just get this from extlib. *)
(* LATER: Sadly, no. Pull request this? *) 
(** To write a generator for well-typed states given a context
    [Gamma], we use the QuickChick combinator 
    [sequenceGen : list (G A) -> G (list A)], which takes a list of
    generators and produces a generator for lists.
  
    We just need to iterate ([map]) through the context, producing an
    arbitrary value of the appropriate type for each pair [(x,T)]. The
    [sequenceGen] combinator will then chain all those generators in
    sequence, producing a generator for well-typed states *)
    
Definition gen_well_typed_state (Gamma : context) : G state := 
  sequenceGen (List.map (fun '(x, T) =>
                           v <- gen_typed_value T;;
                           ret (x, v)) Gamma).

(** * Evaluation *)

(** The evaluation function takes a state and an expression and
    returns an optional value, which can be [None] if the expression
    encounters a dynamic type error like trying to perform addition on
    a boolean. *)

(* SOONER: Could/should this be written monadically?  (BCP: Probably
   both.) *)
Fixpoint eval (st : state) (e : exp) : option value :=
  match e with
  | EVar x => map_get st x
  | ENum n => Some (VNat n)
  | EPlus e1 e2 => 
    match eval st e1, eval st e2 with 
    | Some (VNat n1), Some (VNat n2) => Some (VNat (n1 + n2))
    | _, _ => None
    end 
  | EMinus e1 e2 => 
    match eval st e1, eval st e2 with 
    | Some (VNat n1), Some (VNat n2) => Some (VNat (n1 - n2))
    | _, _ => None
    end
  | EMult e1 e2 => 
    match eval st e1, eval st e2 with 
    | Some (VNat n1), Some (VNat n2) => Some (VNat (n1 * n2))
    | _, _ => None
    end
  | ETrue       => Some (VBool true  )
  | EFalse      => Some (VBool false )
  | EEq e1 e2 => 
    match eval st e1, eval st e2 with 
    | Some (VNat n1), Some (VNat n2) => Some (VBool (n1 =? n2))
    | _, _ => None
    end
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
    end
  end.

(** We will see in a later chapter (\CHAP{QuickChickTool}) how we can
    use QuickChick to introduce such _mutations_ and have them
    automatically checked. *)

(** TERSE: *** *)
(** _Type soundness_ states that, if we have an expression [e] of a
    given type [T] as well as a well-typed state [st], then evaluating
    [e] in [st] will never fail.*)

Definition isNone {A : Type} (m : option A) :=
  match m with 
  | None => true
  | Some _ => false
  end.

(* SOONER: Coq 8.8 supports nicer notation for tests like "isNone" *)
Conjecture expression_soundness : forall Gamma st e T,  
    well_typed_state Gamma st ->  Gamma ||- e \IN T ->
    isNone (eval st e) = false.

(** To test this property, we construct an appropriate checker: *)

Definition expression_soundness_exec := 
  let num_vars := 4 in 
  let top_level_size := 3 in
  forAll (gen_context num_vars)  (fun Gamma =>
  forAll (gen_well_typed_state Gamma) (fun st =>
  forAll arbitrary (fun T =>                                    
  forAll (gen_exp_typed_sized 3 Gamma T) (fun me => 
  match me with  
  | Some e => negb (isNone (eval st e))
  | _ => true
  end)))).   

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

(** Let's see what happens if we use the default shrinker for
    expressions carelessly. *)

Derive Shrink for exp.

Definition expression_soundness_exec_firstshrink := 
  let num_vars := 4 in 
  let top_level_size := 3 in
  forAll (gen_context num_vars)  (fun Gamma =>
  forAll (gen_well_typed_state Gamma) (fun st =>
  forAll arbitrary (fun T =>                                    
  forAllShrink (gen_exp_typed_sized 3 Gamma T) shrink (fun me => 
  match me with  
  | Some e => negb (isNone (eval st e))
  | _ => true
  end)))).   

(* QuickChick expression_soundness_exec_firstshrink. *)
(** 
<< 
     ===> 
       QuickChecking expression_soundness_exec_firsttry
       [(1,TBool), (2,TNat), (3,TBool), (4,TBool)]
       [(1,VBool false), (2,VNat 0), (3,VBool true), (4,VBool false)]
       TBool
       Some EAnd (ENum 0) ETrue
       *** Failed after 28 tests and 7 shrinks. (0 discards)
>>
*)

(** The expression shrank to something ill-typed! Since it causes the
    checker to fail, QuickChick views this as a succesfull shrink, even 
    though this could not actually be produced by our generator and 
    doesn't satisfy our preconditions!  One solution would be to check 
    the preconditions in the Checker, filtering out shrinks.  But that 
    would be inefficient. *)
(* SOONER: How inefficient?? I'm not convinced. *)

(** TERSE: *** *)

(* HIDE: Another option we didn't consider explicitly is to make
   just the shrinker check that things are well typed.  This will slow
   down shrinking, but not testing.  We should implement this variant,
   show how it performs, and discuss the comparison. *)
(* HIDE: That is almost the same thing. The slowdown does not come 
   from having to check if something is well typed, it comes from 
   generating "too many" candidate shrinks. *)
(* HIDE: BCP: I still want to see some numbers! *)
(* LATER: Add this experiment. *)
(** We not only need to shrink expressions, we need to shrink them so
    that their type is preserved! To accomplish this, we need to
    intuitively follow the opposite of the procedure we did for
    generators: look at a typing derivation and see what parts of it
    we can shrink to while maintaining their types so that the type of
    the entire thing is preserved.
  
    As in the case of [gen_exp_typed], we are going to build up the
    full shrinker in steps. Let's begin with shrinking constants.

    - If [e = ENum x] for some [x], all we can do is try to shrink
      [x].
    - If [e = ETrue] or [e = EFalse], we could shrink it to the other.
      But remember, we don't want to do both, as this would lead to an
      infinite loop in shrinking!  We choose to shrink [EFalse] to
      [ETrue]. *)

Definition shrink_base (e : exp) : list exp :=
  match e with 
  | ENum n => map ENum (shrink n)
  | ETrue => []
  | EFalse => [ETrue] 
  | _ => []
  end.

(** TERSE: *** *)
(** The next case, [EVar], must take the type [T] to be preserved into
    account. To shrink an [EVar] we could try shrinking the inner
    identifier, but shrinking an identifier by shrinking its natural
    number representation makes little sense. Better, we can try to 
    shrink the [EVar] to a constant of the appropriate type. *)

Definition shrink_evar (T : ty) (e : exp) : list exp :=
  match e with 
  | EVar x => 
    match T with 
    | TNat => [ENum 0]
    | TBool => [ETrue ; EFalse]
    end
  | _ => []
  end.

(** TERSE: *** *)
(** Finally, we need to be able to shrink the recursive cases. Consider 
    [EPlus e1 e2]: 
      - We could try (recursively) shrinking [e1] or [e2] preserving their 
        [TNat] type.
      - We could try to shrink directly to [e1] or [e2] since their type 
        is the same as [EPlus e1 e2]. *)

(** On the other hand, consider [EEq e1 e2]:
      - Again, we could recursively shrink [e1] or [e2].
      - But we can't shrink _to_ [e1] or [e2] since they are of a
        different type.
      - For faster shrinking, we can also try to shrink such expressions
        to boolean constants directly. *)

Fixpoint shrink_rec (T : ty) (e : exp) : list exp := 
  match e with 
  | EPlus e1 e2 => 
    e1 :: e2 
       :: (List.map (fun e1' => EPlus e1' e2) (shrink_rec T e1))
       ++ (List.map (fun e2' => EPlus e1 e2') (shrink_rec T e2))
  | EEq e1 e2 => 
    ETrue :: EFalse 
       :: (List.map (fun e1' => EEq e1' e2) (shrink_rec TNat e1))
       ++ (List.map (fun e2' => EEq e1 e2') (shrink_rec TNat e2))
  | _ => []
  end.

(** TERSE: *** *)
(** Putting it all together yields the following smart shrinker: *)
   
Fixpoint shrink_exp_typed (T : ty) (e : exp) : list exp :=
  match e with 
  | EVar _ => 
    match T with 
    | TNat => [ENum 0]
    | TBool => [ETrue ; EFalse]
    end
  | ENum _ => []
  | ETrue => []
  | EFalse => [ETrue]
  | EPlus e1 e2 => 
    e1 :: e2 
       :: (List.map (fun e1' => EPlus e1' e2) (shrink_exp_typed T e1))
       ++ (List.map (fun e2' => EPlus e1 e2') (shrink_exp_typed T e2))
  | EMinus e1 e2 => 
    e1 :: e2 :: (EPlus e1 e2)
       :: (List.map (fun e1' => EMinus e1' e2) (shrink_exp_typed T e1))
       ++ (List.map (fun e2' => EMinus e1 e2') (shrink_exp_typed T e2))
  | EMult e1 e2 => 
    e1 :: e2 :: (EPlus e1 e2)
       :: (List.map (fun e1' => EMult e1' e2) (shrink_exp_typed T e1))
       ++ (List.map (fun e2' => EMult e1 e2') (shrink_exp_typed T e2))
  | EEq e1 e2 => 
    ETrue :: EFalse 
       :: (List.map (fun e1' => EEq e1' e2) (shrink_exp_typed TNat e1))
       ++ (List.map (fun e2' => EEq e1 e2') (shrink_exp_typed TNat e2))
  | ELe e1 e2 => 
    ETrue :: EFalse :: (EEq e1 e2)
       :: (List.map (fun e1' => ELe e1' e2) (shrink_exp_typed TNat e1))
       ++ (List.map (fun e2' => ELe e1 e2') (shrink_exp_typed TNat e2))
  | ENot e => 
    ETrue :: EFalse :: e :: (List.map ENot (shrink_exp_typed T e))
  | EAnd e1 e2 => 
    ETrue :: EFalse :: e1 :: e2 
       :: (List.map (fun e1' => EAnd e1' e2) (shrink_exp_typed TBool e1))
       ++ (List.map (fun e2' => EAnd e1 e2') (shrink_exp_typed TBool e2))
  end.

(** TERSE: *** *)
(** As we saw for generators, we can also perform sanity checks on our
    shrinkers.  Here, when the shrinker is applied to an expression of
    a given type, all of its results should have the same type. *)
    
Definition shrink_typed_has_type :=
  let num_vars := 4 in
  let top_level_size := 3 in 
  forAll (gen_context num_vars) (fun Gamma =>
  forAll arbitrary (fun T =>                                   
  forAll (gen_exp_typed_sized top_level_size Gamma T) (fun me =>
  match me with 
  | Some e => 
    List.forallb (fun e' => (has_type Gamma e' T)?) (shrink_exp_typed T e)
  | _ => false 
  end))).

(* QuickChick shrink_typed_has_type. *)

(** ** Back to Soundness *)
(** To lift the shrinker to optional expressions, QuickChick provides
    the following function. *)

Definition lift_shrink {A}
              (shr : A -> list A) (m : option A) 
           : list (option A) :=
  match m with 
  | Some x => List.map Some (shr x)
  | _ => []
  end.

(** Armed with shrinking, we can pinpoint the bug in the [EAnd] branch
    of the evaluator. *)

Definition expression_soundness_exec' := 
  let num_vars := 4 in 
  let top_level_size := 3 in
  forAll (gen_context num_vars)  (fun Gamma =>
  forAll (gen_well_typed_state Gamma) (fun st =>
  forAll arbitrary (fun T =>                                    
  forAllShrink (gen_exp_typed_sized 3 Gamma T) 
               (lift_shrink (shrink_exp_typed T)) 
               (fun me =>  
  match me with  
  | Some e => negb (isNone (eval st e))
  | _ => true
  end)))).   

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

Derive Show for com.

(** (Of course, the derived [Show] instance is not going to use these
    notations!) *)
(* LATER: Could it? *)
(* LATER: I don't believe that's possible. Would require a lot of engineering
   to check if any pattern can be expressed via a notation in the database. *)
(** TERSE: *** *)

(** We can now define what it means for a command to be well typed
    for a given context. The interesting cases are [TAss] and [TIf]/[TWhile]. 
    The first one, ensures that the type of the variable we are 
    assigning to is the same as that of the expression. The latter,
    requires that the conditional is indeed a boolean expression.
 *)

Inductive well_typed_com : context -> com -> Prop :=
  | TSkip : forall Gamma, well_typed_com Gamma CSkip
  | TAss  : forall Gamma x e T, 
      bound_to Gamma x T -> 
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
(** ** Decidable instance for well-typed. *)

(** A couple of lemmas and a custom tactic will help the decidability
    proof... *)

Lemma bind_deterministic Gamma x (T1 T2 : ty) :
  bound_to Gamma x T1 -> bound_to Gamma x T2 -> 
  T1 = T2.
(* FOLD *)
Proof.
  destruct T1; destruct T2; intros H1 H2; eauto; 
    inversion H1; inversion H2; congruence.
Qed.
(* /FOLD *)

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

Ltac solve_det := 
  match goal with 
  | [ H1 : bound_to _ _ ?T1 ,
      H2 : bound_to _ _ ?T2 |- _ ] =>
    assert (T1 = T2) by (eapply bind_deterministic; eauto)
  | [ H1 : has_type _ _ ?T1 ,
      H2 : has_type _ _ ?T2 |- _ ] =>
    assert (T1 = T2) by (eapply bind_deterministic; eauto)
  end.
(* TERSE: /HIDEFROMHTML *)

(** Now, here is a brute-force decision procedure for the typing
    relation (which amounts to a simple typechecker). *) 

Instance dec_well_typed_com (Gamma : context) (c : com) 
  : Dec (well_typed_com Gamma c).
(* FOLD *)
Proof with eauto.
  constructor. unfold ssrbool.decidable.
  induction c; solve_sum.
  - destruct (dec_bound_to Gamma i TNat); destruct dec;
    destruct (dec_has_type e Gamma TNat); destruct dec; 
    destruct (dec_bound_to Gamma i TBool); destruct dec;
    destruct (dec_has_type e Gamma TBool); destruct dec; solve_sum;
    try solve_det; try congruence;
    right; intro Contra; inversion Contra; subst; clear Contra;
    try solve_det; try congruence;
    destruct T; eauto.
  - destruct IHc1; destruct IHc2; subst; eauto; solve_sum.
  - destruct IHc1; destruct IHc2; subst; eauto; solve_sum.
    destruct (dec_has_type e Gamma TBool); destruct dec; solve_sum.
  - destruct IHc; 
    destruct (dec_has_type e Gamma TBool); destruct dec; solve_sum.
Qed.
(* /FOLD *)

(* FULL *)
(* EX4M (arbitrary_well_typed_com) *)
(** Write a generator and a shrinker for well_typed programs given
    some context [Gamma].  Write some appropriate sanity checks and
    make sure they give expected results. *)

(* SOLUTION *)
Fixpoint gen_com_typed_sized (size : nat) (Gamma : context) : GOpt com :=
  let assgn := 
                (List.map (fun '(x,T) =>
                             (1, e <- gen_exp_typed_sized size Gamma T;;
                                ret (CAss x e)))
                          Gamma)
  in 
  let skip :=
      ret SKIP in
  let recs size' := 
      [ (1, c1 <- gen_com_typed_sized size' Gamma;;
            c2 <- gen_com_typed_sized size' Gamma;;
            ret (CSeq c1 c2))
      ; (1, c <- gen_com_typed_sized size' Gamma;;
            b <- gen_exp_typed_sized size' Gamma TBool;;
            ret (CWhile b c))
      ; (1, b <- gen_exp_typed_sized size' Gamma TBool;;
            c1 <- gen_com_typed_sized size' Gamma;;
            c2 <- gen_com_typed_sized size' Gamma;;
            ret (CIf b c1 c2))
      ] in
  match size with 
  | O => backtrack ((1, skip) :: assgn)
  | S size' => backtrack ((1, skip) :: (assgn ++ recs size'))
  end.

Fixpoint shrink_com_typed (Gamma : context) (c : com) : list com := 
  match c with 
  | SKIP => []
  | CAss x e => 
    match map_get Gamma x with
    | Some T => SKIP :: List.map (fun e' => CAss x e) (shrink_exp_typed T e)
    | _ => []
    end
  | CSeq c1 c2 =>
    c1 :: c2 
       :: (List.map (fun c1' => CSeq c1' c2) (shrink_com_typed Gamma c1))
       ++ (List.map (fun c2' => CSeq c1 c2') (shrink_com_typed Gamma c2))
  | CIf b c1 c2 =>
    c1 :: c2 
       :: (List.map (fun c1' => CIf b c1' c2) (shrink_com_typed Gamma c1))
       ++ (List.map (fun c2' => CIf b c1 c2') (shrink_com_typed Gamma c2))
       ++ (List.map (fun b' => CIf b' c1 c2) (shrink_exp_typed TBool b))
  | CWhile b c =>
    c :: (CIf b c c) 
      :: (List.map (fun b' => CWhile b' c) (shrink_exp_typed TBool b))
      ++ (List.map (fun c' => CWhile b c') (shrink_com_typed Gamma c))
  end.

Definition gen_com_typed_has_type :=
  let num_vars := 4 in
  let top_level_size := 3 in 
  forAll (gen_context num_vars) (fun Gamma =>
  forAll (gen_well_typed_state Gamma) (fun st =>
  forAllShrink (gen_com_typed_sized 3 Gamma) 
               (lift_shrink (shrink_com_typed Gamma)) 
               (fun mc => 
  match mc with 
  | Some c => (well_typed_com Gamma c)?
  | _ => false (* this should NEVER fail *)
  end))).

(* QuickChick gen_com_typed_has_type. *)

Definition shrink_com_has_type :=
  let num_vars := 4 in
  let top_level_size := 3 in 
  forAll (gen_context num_vars) (fun Gamma =>
  forAll (gen_well_typed_state Gamma) (fun st =>
  forAllShrink (gen_com_typed_sized 3 Gamma) 
               (lift_shrink (shrink_com_typed Gamma)) 
               (fun mc => 
  match mc with 
  | Some c => 
    List.forallb (fun c' => (well_typed_com Gamma c')?) 
                 (shrink_com_typed Gamma c)
  | _ => false (* this should NEVER fail *)
  end))).

(* QuickChick shrink_com_has_type. *)

(* /SOLUTION *)
(** [] *)
(* /FULL *)

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
   

(** * Automation (Revisited) *)

(** QuickChick is under very active development.  Our vision is that
    it should automate most of the tedious parts of testing, while
    retaining full customizability.

    We close this case study with a brief demo of some things it can
    do now. *)

(** Recall the [has_type_value] property and its corresponding generator:
[[
  Inductive has_type_value : value -> ty -> Prop :=
    | TyVNat  : forall n, has_type_value (VNat  n) TNat
    | TyVBool : forall b, has_type_value (VBool b) TBool.

  Definition gen_typed_value (T : ty) : G value :=
    match T with 
    | TNat  => n <- arbitrary;; ret (VNat n)
    | TBool => b <- arbitrary;; ret (VBool b)
    end.
]]
    QuickChick includes a derivation mechanism that can _automatically_
    produce such generators -- i.e., generators for data structures 
    satisfying inductively defined properties! *)

Derive ArbitrarySizedSuchThat for (fun v => has_type_value v T).
(** ===> 
  GenSizedSuchThathas_type_value is defined. *)

(** TERSE: *** *)
(** Let's take a closer look at what is being generated (after 
    doing some renaming and reformatting). *)

Print GenSizedSuchThathas_type_value.
(** <<
     ===>
       GenSizedSuchThathas_type_value = fun T : ty =>
       {| arbitrarySizeST := 
          let fix aux_arb (size0 : nat) (T : ty) {struct size0} 
                : G (option value) :=
            match size0 with
            | 0 => backtrack [(1, match T with
                                  | TBool => ret None
                                  | TNat => n <- arbitrary;;
                                            ret (Some (VNat n))
                                  end)
                             ;(1, match T with
                                  | TBool => b <- arbitrary;;
                                             ret (Some (VBool b)))
                                  | TNat => ret None
                                  end)]
            | S _ => backtrack [(1, match T with
                                    | TBool => ret None
                                    | TNat => n <- arbitrary;;
                                              ret (Some (VNat n))
                                    end)
                               ;(1, match T with
                                    | TBool => b <- arbitrary;;
                                               ret (Some (VBool b)))
                                    | TNat => ret None
                                    end)]
            end in
            fun size0 : nat => aux_arb size0 T |}

       : forall T : ty,
           GenSizedSuchThat value 
               (fun v => has_type_value v T)
>>
*)

(** This is a rather more verbose version of the [gen_typed_value]
    generator, but the end result is actually exactly the same 
    distribution! *)

(** ** (More) Typeclasses for Generation *)

(** QuickChick provides typeclasses for automating the generation 
    for data satisfying predicates. *)

Module GenSTPlayground.

(** A variant that takes a size,... *)

Class GenSizedSuchThat (A : Type) (P : A -> Prop) := 
  { arbitrarySizeST : nat -> G (option A) }.

(** ...an unsized variant,... *)

Class GenSuchThat (A : Type) (P : A -> Prop) := 
  { arbitraryST : G (option A) }.

(** ...convenient notation,... *)

Notation "'genST' x" := (@arbitraryST _ x _) (at level 70).

(** ...and a coercion between the two: *)

Instance GenSuchThatOfBounded (A : Type) (P : A -> Prop) 
         (H : GenSizedSuchThat A P)
  : GenSuchThat A P := 
  { arbitraryST := sized arbitrarySizeST }.

End GenSTPlayground.

(** ** Using "SuchThat" Typeclasses *)

(** QuickChick can now (ab)use the typeclass resolution mechanism to 
    perform a bit of black magic: *)

Conjecture conditional_prop_example : 
  forall (x y : nat), x = y -> x = y.

(* QuickChick conditional_prop_example. *)
(** <<
  ==>
    QuickChecking conditional_prop_example
    +++ Passed 10000 tests (0 discards)
>>
*)

(** Notice the "0 discards": that means that quickchick is using
    generators that produce [x] and [y] such that [x = y]! *)

(** * Acknowledgements *)

(** The first version of this material was developed in collaboration
    with Nicolas Koh. *)
