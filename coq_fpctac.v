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
  
  type l,j,k          iform.  % atomic formulas = primitive types
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
  prop_list [l,j,k].
}}.

(* Examples translated to MaxCert *)
Elpi Db maxcerts.db lp:{{
  pred maxex o:int, o:cert.
maxex 2 (max zero (max1
 (maxi (ix zero) 
   (max1 (maxi (ix (succ zero)) (max1 (maxi (ix (succ zero)) max0))))))).
}}.

Elpi Db coq_fpc.db lp:{{
  %% Coq terms as proof certificates!
  % pred coq_to_iform i:term, o:iform.
  % coq_to_iform (prod _name (sort prop) T) F :- atomic F.
  % coq_to_iform (prod _name T1 T2) (A imp B) :-
  %   coq_to_iform T1 A,
  %   pi x\ coq_to_iform x A => coq_to_iform T2 B. %% T2 should not be really depending on the abstracted term!
  %% The forall case should be something in the likes of this
  % coq_to_iform (prod _name T1 T2) (A imp B) :-
  %   coq_to_iform T1 A,
  %   pi x\ coq_to_iform x A => coq_to_iform (T2 x) B.
  %% Reminder:
  % type fun  @name -> term -> (term -> term) -> term.         % fun x : t =>
  % type prod @name -> term -> (term -> term) -> term.         % forall x : t,
  % type let  @name -> term -> term -> (term -> term) -> term. % let x : T := v in
  % type app   list term -> term.                   % app [hd|args]
  %% The fpc for lambda terms in DeBrujin
  % kind deb            type.
  % type apply          int -> list deb -> deb.
  % type lc             int ->      deb -> cert.
  % type args           int -> list deb -> cert.    
  % type idx                       int -> index.
  % arr_jc      (lc C D) (lc C D).
  % storeR_jc   (lc C D) (lc C D).
  % releaseR_je (lc C D) (lc C D).
  % storeL_jc   (lc C D) (lc C' D) (idx C) :- C' is C + 1.
  % decideL_je  (lc C (apply H A)) (args C A) (idx V) :- V is C - H - 1.
  % initialL_je (args _C []).
  % arr_je      (args C (A::As)) (lc C A) (args C As).
  type coqcert term -> cert.
  type coqabs  (term -> term) -> cert.
  type hold index -> term -> cert.
  type coqidx  term -> index.
  type tmofidx index -> term.
  arr_jc (coqcert (fun _name _type F)) (x\ hold x (F (tmofidx x))).
  % arr_je (coqcert (app [H,T])) (coqcert T) (coqcert H).
  arr_je (hold Idx (app [tmofidx Idx, A])) (coqcert A) (coqcert (tmofidx Idx)).
  storeL_jc (hold Idx T) (coqcert T) Idx.
  storeR_jc Cert Cert.
  releaseR_je Cert Cert.
  decideL_je (coqcert (app [tmofidx Idx,B] as Tm)) (hold Idx Tm) Idx.
  decideL_je (coqcert (tmofidx Idx as Tm)) (hold Idx Tm) Idx.
  initialL_je _.
}}.

Elpi Tactic coq_fpc.
Elpi Accumulate File "fpc/ljf-polarize.mod".
Elpi Accumulate File "fpc/ljf-lambda.mod".
Elpi Accumulate File "fpc/stlc-fpc.mod".
Elpi Accumulate File "fpc/pairing-fpc.mod".
Elpi Accumulate File "fpc/maximal-fpc.mod".
Elpi Accumulate Db coq_fpc.db.
Elpi Typecheck.
Elpi Debug "DEBUG".
Elpi Query lp:{{
  check (coqcert (fun _ _ (x\ (fun _ _ (y\ app [x, y]))))) (async [] (unk (((n j) arr (n l)) arr (n j) arr (n l)))).
}}.
Elpi Query lp:{{
  check (coqcert (fun _ _ (x\x))) (async [] (unk (((n j) arr (n j)) arr (n j) arr (n j)))).
}}.

Elpi Accumulate Db maxcerts.db.
Elpi Query lp:{{
  ljf_entry (coqcert (fun _ _ (x\ fun _ _ (y\ y)))) ((n l) arr ((n j) arr (n j))).
}}.
Elpi Query lp:{{
  maxex 2 Cert, ljf_entry (Cert <c> coqcert M) ((n l) arr ((n j) arr (n j))).
}}.
 <c> (coqcert M)
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
  type lambda_to_coq tm -> iform -> term -> prop.
  lambda_to_coq (lam X) (T1 imp T2) (fun _name T1' (x\ F x)):-
    iform_to_coq T1 T1',
    pi x y\ lambda_to_coq x T1 y =>
      lambda_to_coq (X x) T2 (F y).
  lambda_to_coq (ap X Y) Ty (app [X',Y']):-
    lambda_to_coq X (T imp Ty) X',
    lambda_to_coq Y T Y'.

  %% The main predicate. Select the example, translate the lambda term to Coq.
  solve [int N] [goal Ctx Ev Ty _] [] :- 
    prop_list L, example N Tm Form, prop_to_coq Tm Form L Ev.
}}. 
Elpi Typecheck.

(*Time for tests!*)
(*Some tests on the lambda Prolog code*)
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
Elpi Query lp:{{
  prop_to_coq (lam x\ lam y\ ap x y) ((l imp j) imp (l imp j)) [l,j] X.
}}.
(*Elpi Query lp:{{
  prop_to_coq (lam x\ lam y\ ap x y) ((l imp j) imp (l imp j)) [l,j] (fun `A` (sort prop) c0 \ fun `B` (sort prop) c1 \ fun `H` (prod `_` c0 c2 \ c1) c2 \ fun `J` c0 c3 \ app [c2, c3]).
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
Lemma example3 : forall A B : Prop, (A -> B) -> (A -> B).
elpi id.
elpi fpc 3.
Qed.
Lemma example4 : forall A B : Prop, A -> (B -> ((A -> A) -> A)).
elpi fpc 4.
Qed.
Lemma example5 : forall A B C : Prop, A -> ((((A->B)->B)->C)->C).
elpi fpc 5.
Qed.
Lemma example6 : forall A B C : Prop, B -> ((((A->B)->B)->C)->C).
elpi fpc 6.