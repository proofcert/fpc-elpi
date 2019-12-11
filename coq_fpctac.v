From elpi Require Import elpi.

(*A "tactic" that will print context and goal *)
Elpi Tactic id.
Elpi Accumulate lp:{{
  solve _ [goal Ctx Ev Ty _] _ :-
    coq.say "goal" Ev "is\n" Ctx "\n-------\n" Ty.
}}. 

(*The examples Database, put here for simpler extensibility*)
Elpi Db lambda.db lp:{{
  kind iform, i       type.
  type imp            iform -> iform -> iform.
  type forall         (i -> iform) -> iform.
  type tt, ff         iform.
  type and, or        iform -> iform -> iform.
  type exists         (i -> iform) -> iform.
  infixr and  6.
  infixr or   5.
  infixr imp  4.
  kind tm             type.
  type app            tm -> tm -> tm.
  type lam            (tm -> tm) -> tm.
  
  type debi           int -> tm -> deb -> prop.
  type debe           int -> tm -> int -> (list deb -> list deb) -> prop.
  type vr             int -> tm -> prop.
  
  type i,j,k          iform.  % atomic formulas = primitive types
  type atomic, non_atomic                   iform -> prop.
  non_atomic tt         & non_atomic ff.
  non_atomic (_ and _)  & non_atomic (_ or _)  &  non_atomic (_ imp _).
  non_atomic (forall _) & non_atomic (exists _).

  atomic A :- non_atomic A, !, fail.  % NAF here.
  atomic _A.
  example 1 (lam x\x) (l imp l).
  example 2 (lam x\ lam y\ y) (j imp (l imp l)).
  example 3 (lam x\ lam y\ ap x y) ((l imp j) imp (l imp j)).
  example 4 (lam x\ lam y\ lam z\ ap z (ap z x)) (l imp (j imp ((l imp l) imp l))).
  example 5 (lam x\ lam y\ ap y (lam z\ ap z x)) (l imp ((((l imp j) imp j) imp k) imp k)).
  example 6 (lam x\ lam y\ ap y (lam z\ ap z x)) (j imp ((((l imp j) imp j) imp k) imp k)).
  pred off i:tm, o:iform.
  off (ap M N) A       :- off M (B imp A), off N B.
  off (lam R) (A imp B) :- pi x\ off x A => off (R x) B.
  %% The available propositional contexts, for the solver to look into.
  prop_list [l].
  prop_list [l,j].
  prop_list [j,k,l].
}}.

(* Examples translated to MaxCert *)
Elpi Db maxcerts.db lp:{{
  pred maxex o:int, o:cert.
maxex 2 (max zero (max1
 (maxi (ix zero) 
   (max1 (maxi (ix (succ zero)) (max1 (maxi (ix (succ zero)) max0))))))).
}}.

Elpi Tactic fpc.
Elpi Accumulate File "fpc/ljf-polarize.mod".
Elpi Accumulate File "fpc/ljf-kernel.mod".
Elpi Accumulate File "fpc/stlc-fpc.mod".
Elpi Accumulate File "fpc/pairing-fpc.mod".
Elpi Accumulate File "fpc/maximal-fpc.mod".
Elpi Accumulate Db lambda.db.
Elpi Accumulate Db maxcerts.db.
Elpi Accumulate lp:{{
  %% Remember the eigenvariable associated to a Coq variable
  pred prop_name i:iform, o:term.
  %% Transform formulas to Coq formulas
  pred iform_to_coq i:iform, o:term.
  iform_to_coq X Y :-
    prop_name X Y.
  iform_to_coq (X imp Y) {{lp:X' -> lp:Y'}}:-
    iform_to_coq X X',
    iform_to_coq Y Y'.
  %% The main predicate transforming a term with formula and list of prop. variables
  %% to a Coq term. This covers the introduction of the propositional variables, and
  %% then calls the next predicate.
  pred prop_to_coq i:tm, i:iform, i:list iform, o:term.
  prop_to_coq Tm Iform [V|Tail] (fun _name (sort prop) F) :-
    pi x\ prop_name V x => 
      prop_to_coq Tm Iform Tail (F x).
  prop_to_coq Tm Iform [] Term :-
    lambda_to_coq Tm Iform Term.
  %% The predicate translating the term with formula to a Coq term
  pred lambda_to_coq i:tm, i:iform, o:term.
  lambda_to_coq (lam X) (T1 imp T2) (fun _name T1' (x\ F x)):-
    iform_to_coq T1 T1',
    pi x y\ lambda_to_coq x T1 y =>
      lambda_to_coq (X x) T2 (F y).
  % Not working at the moment
  % lambda_to_coq (ap X Y) Ty (app [X',Y']):-
  %   lambda_to_coq X (T imp Ty) X',
  %   lambda_to_coq Y T Y'.

  %% The main predicate. Select the example, translate the lambda term to Coq.
  solve [int N] [goal Ctx Ev Ty _] [] :- 
    prop_list L, example N Tm Form, prop_to_coq Tm Form L Ev.
}}. 
Elpi Typecheck.

(*Time for tests!*)
(*Some tests on the lambda Prolog code*)
Elpi Trace "lambda_to_coq".
Elpi Query lp:{{
  prop_to_coq (lam x\x) (j imp j) [j] X.
  }}.
Elpi Query lp:{{
  prop_to_coq (lam x\x) (j imp j) [j] {{fun (A : Prop) (H : A) => H)}}.
  }}.
Elpi Query lp:{{
  prop_to_coq (lam x\ lam y\ lam z\ x) (j imp k imp l imp j) [j,k,l] X.
}}.
Elpi Query lp:{{
  prop_to_coq (lam x\ lam y\ lam z\ x) (j imp k imp l imp j) [j,k,l] {{(fun (A B C : Prop) (H : A) (_ : B) (_ : C) => H)}}.
}}.
Elpi Query lp:{{prop_to_coq (lam x\ lam y\ y) (j imp (l imp l)) [l,j] {{(fun (A B : Prop) (_ : B) (H0 : A) => H0)}}.
}}.
(*Elpi Query lp:{{
  prop_to_coq (lam x\ lam y\ ap x y) ((l imp j) imp (l imp j)) [l,j] X.
}}. *)

(* Elpi Accumulate lp:{{
test_all :-
   example X Tm Ty, 
   (sigma Str\ term_to_string X Str, coq.say Str, coq.say " "),
   if (lambda_to_coq Tm Ty _)
      (coq.say "Success\n")
      (coq.say "Fail\n"),
  fail.
}}.
Elpi Query lp:{{test_all.}}.

(* Here I would like to test extracting lambda terms from maxcerts *)
Elpi Query "example 1 Tm Ty, debi 0 Tm Deb, polarize- Ty Form, ljf_entry ((lc 0 Deb) <c> (max _ M)) Form.".
Elpi Query lp:{{
maxex N Cert, example N _ Ty, polarize- Ty Form, ljf_entry (Cert <c> (lc 0 Deb)) Form.
% debi 0 Tm Deb,
}}.
*)

(*Now we test the fpc tactic in Coq proofs!*)
Lemma example1 : forall A : Prop, A -> A.
elpi fpc 1.
Show Proof.
Qed.
Lemma example2 : forall A B : Prop, B -> (A -> A).
elpi fpc 2.
Show Proof.
Qed.
Lemma example3 : forall A B : Prop, (B -> A) -> (B -> A).
elpi fpc 3.
  example 3 (lam x\ lam y\ ap x y) ((l imp j) imp (l imp j)).