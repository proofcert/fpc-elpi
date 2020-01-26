From elpi Require Import elpi.

(*Simply prints context and goal, doesn't solve anything *)
Elpi Tactic id.
Elpi Accumulate lp:{{
  solve _ [goal Ctx Ev Ty _] _ :-
    coq.say "goal" Ev "is\n" Ctx "\n-------\n" Ty.
}}. 

(*
   Database notes
   ==============

   Design overview
   ---------------

   The runtime of coq-elpi calls into the standard `solve` entrypoint. From this
   point, we call `bootstrap` to set up the tactic and execute it (here, `Ev`
   needs to be unified with a term, and `Nat` is the depth bound that will be
   used to control the exploration of the search space).

   The bootstrapping predicate recursively traverses the goal, abstracting over
   sort `prop` and introducing the propositional variables as needed as clauses
   of the predicate `prop_names` (initially empty) assumed by hypothetical
   reasoning (as the context of the goal was before the call to `bootstrap`).
   The boostrapping process also introduces clauses of `abs_name` for names of
   first-order predicates. The distinction between the two kinds of names comes
   down to the fact that the current design can only handle unary names;
   ideally, we will have ways of creating names of arbitrary arities, even
   though at the moment we use the "uncurried" form just described.

   At the end of the process, `bootstrap` has introduced both kinds of
   components to the environment and proceeds to check whether the goal is an
   actual formula (so we are not introducing names any more), in which case it
   calls `coq_to_iform`, which reifies the goal into an intuitionistic formula
   of the object logic, and finally calls the FPC checker.

   We define the logical connectives `and`, `or`, `imp` `to reify a subset of
   terms of Coq (roughly, those that represent first-order formulas) into
   formulas of the object logic in the usual manner.

   Observe that the universal quantifier `forall` results from the reification
   by `coq_to_iform` of the non-dependent case of the Coq produc type, when
   applied to a term of type `Type` (the identifiers `sort`, `typ`... are Elpi's
   own names for those, with the underscore following `typ` in place of the
   parameter used to denote type universes). There is one curious issue related
   to this step (fine for now?): in the treatment of type universes, if these
   are manipulated only using quoted Coq syntax in a λProlog environment, they
   remain logic variables; they are only instantiated while inside the proof
   proper, say by applying a tactic. This can lead to some parsing problems down
   the line.

   Terms are embedded into certificates via `coqcert` and `coqabs`. This last
   constructor is particularly interesting, as it performs an explicit "deep
   embedding" of the abstraction instead of relying on the abstraction
   mechanisms of the `term` type proper. This is especially relevant for the
   handling of the universal clerk: in it, terms get decomposed into two
   components; it is important to note that the store rule is the one charged
   with creating the eigenvariable (which requires a small modification in the
   standard FPC checker).

   The clerks and experts of the built-in FPC certificate definition treat
   certificates of the two forms just described. Surprisingly, there is little
   to no duplication in these, and a pleasing symmetry seems apparent, though it
   needs to be ascertained carefully.

   Comments
   --------

   The `hold` certificate constructor is vestigial of a former design, and no
   longer used.

   Throughout the code, two different but a priori equivalent coding conventions
   to manipulate Coq terms are maintained for technical reasons: on the one
   hand, the quoting mechanism notation `{{ }}` where λProlog variables are
   denoted by `lp:`; on the other, direct use of explicit HOAS. Compare, for
   example, the three clauses of `coq_to_iform` that treat the standard logical
   connectives and the subsequent clause that deals with function application.
   In principle, the latter could also be phrased in terms of the quoted syntax,
   but the result would arguably be less legible. Moreover, in the case of the
   existential quantifier we encounter some parsing issues while following the
   quoted approach. (See also comments on universal quantification above.)

   Consider the FPC definition of `and_jc` referenced above. This clerk is only
   defined for `coqabs` because we expect that it should treat an abstracted
   variable where the projection should be put.

   The negative conjunction should be a let: deconstructing the conjunction,
   where instead of the let construct, one performs the substitution directly.

   Connection between Coq `abs` and open binders.
*)
Elpi Db coq_fpc.db lp:{{
  infixr and  6.
  infixr or   5.
  infixr imp  4.
  type coqcert term -> cert.
  type coqabs  (term -> term) -> cert.
  type hold index -> (term -> term) -> cert.
  type idxoftm term -> index.
  pred prop_name o:term, o:iform.
  % atomic X :- prop_name _ X.
  type coq_to_iform term -> iform -> prop.
  :if "DEBUG" coq_to_iform A B :- announce (coq_to_iform A B).
  coq_to_iform X Y :-
    prop_name X Y.
  coq_to_iform {{lp:X -> lp:Y}} (X' imp Y') :-
    coq_to_iform X X',
    coq_to_iform Y Y'.
  coq_to_iform {{lp:X /\ lp:Y}} (X' and Y') :-
    coq_to_iform X X',
    coq_to_iform Y Y'.
  coq_to_iform {{lp:X \/ lp:Y}} (X' or Y') :-
    coq_to_iform X X',
    coq_to_iform Y Y'.
  coq_to_iform  (app [global Ex_indt, _, (fun _ _ T)]) (exists T') :- 
    coq.locate "ex" Ex_indt,
    % pi x y\ term_to_i x y => %% I am now trying to use coq terms in formulas, so this is not needed
    pi x\ coq_to_iform (T x) (T' x).
  coq_to_iform (prod _ (sort (typ _)) T) (forall T') :-
    % pi x y\ term_to_i x y => %% I am now trying to use coq terms in formulas, so this is not needed
    pi x\  coq_to_iform (T x) (T' x).
  coq_to_iform (app [X,Y]) T:-
    % term_to_i Y Y', %% I am now trying to use coq terms in formulas, so this is not needed
    abs_name X X',
    T = (X' Y).
  type bootstrap term -> term -> nat -> prop.
  :if "DEBUG" bootstrap A B N :- announce (bootstrap A B N).
  bootstrap (prod _ (prod _ (sort (typ _)) (x\ sort prop)) Ty) (fun _ (prod _ (sort (typ _)) (x\ sort prop)) F) N:-
    pi x y z\ abs_name x y =>
      bootstrap (Ty x) (F z) N.
  bootstrap (prod _ (sort prop) Ty) (fun _ (sort prop) F) N:-
    pi x y z\ prop_name x y =>
      bootstrap (Ty x) (F z) N.
  bootstrap Type Term N :-
    (Type = {{lp:_ /\ lp:_}}; Type = {{lp:_ \/ lp:_}}; Type = {{lp:_ -> lp:_}}; Type = (prod _ (sort (typ _)) _)),
    coq_to_iform Type Form,
    polarize- Form PForm, ljf_entry (<c> (dd N) (coqcert Term)) PForm.
  arr_jc (coqcert (fun _name _type F)) (coqabs F).
  arr_je (coqabs (x\ app [x,T])) (coqcert T) (coqabs (x\ x)).
  storeL_jc (coqabs T) (x\ coqcert (T x)) (x\ idxoftm x).
  decideL_je (coqcert (app [Hd,B])) (coqabs (x\ app [x,B])) (idxoftm Hd).
  decideL_je (coqcert Hd) (coqabs (x\ x)) (idxoftm Hd).
  decideL_je (coqcert {{and_ind lp:T lp:Idx}}) (coqabs (x\ {{and_ind lp:T lp:x}})) (idxoftm Idx).
  initialL_je _.
  % initialR_je _ _.
  releaseL_je Cert Cert. %% This should move from a coqabs to a coqcert?
  storeR_jc (coqcert T) (coqcert T).
  releaseR_je Cert Cert.
  decideR_je Cert Cert.
  or_je (coqcert {{or_introl lp:T}}) (coqcert T) left.
  or_je (coqcert {{or_intror lp:T}}) (coqcert T) right.
  % or_jc (coqabs (x\ app [global (const «or_ind» ), _, _, _, (fun _ _ T1), (fun _ _ T2), x])) (coqabs T1) (coqabs T1).
  or_jc (coqabs (x\ {{or_ind lp:{{fun _ _ T1}} lp:{{fun _  _ T2}} lp:x}})) (coqabs T1) (coqabs T1).
  andNeg_jc (coqcert {{conj lp:T1 lp:T2}}) (coqcert T1) (coqcert T2).
  % Instead of using a let-expression, we substitute into the term. Is this good enough?
  andNeg_je (coqabs T) (coqabs (x\ T {{proj1 lp:x}})) left.
  andNeg_je (coqabs T) (coqabs (x\ T {{proj2 lp:x}})) right.
  %% TODO: andPos will be needed, especially in case we want to host classical logic
  % andPos_jc (coqabs (x\ {{and_ind lp:{{fun _ _ (x\ fun _ _ (y\ T))}} lp:x}})) (coqabs (x\ (y\ T))).
  % andPos_je (coqcert T) (coqcert T) (coqcert T).
  all_jc (coqcert (fun _ _ F)) (x\ coqcert (F x)). 
  all_je (coqabs (x\ app [x, T])) (coqcert T) Term.
  some_je (coqcert {{ex_intro lp:Pred lp:Witness lp:Proof}}) (coqcert Proof) Witness.
  some_jc (coqabs (x\ app [x, T])) (x\ coqcert (app [x, T])).
  solve [(int N)] [goal Ctx Ev Ty _] [] :-
    int_to_nat N Nat,
    Ctx => bootstrap Ty Ev Nat.
}}.

Elpi Tactic coq_fpc.
Elpi Accumulate File "fpc/iforms.mod".
Elpi Accumulate File "fpc/iforms.sig".
Elpi Accumulate File "fpc/ljf-polarize.mod".
Elpi Accumulate File "fpc/ljf-lambda.mod".
Elpi Accumulate File "fpc/pairing-fpc.mod".
Elpi Accumulate File "fpc/dd-fpc.mod".
Elpi Accumulate Db coq_fpc.db.
Elpi Typecheck.

Elpi Debug "DEBUG".
(* Elpi Trace. *)

(* These queries with disjunction -- including synthesizing a term -- work.
However the tactic fails with an assertion violation in coq-elpi... *)
Elpi Query lp:{{bootstrap {{forall A : Prop, A \/ A -> A}}
                          {{(fun (A : Prop) (H : A \/ A) => or_ind (fun H0 : A => H0) (fun H0 : A => H0) H)}}
                          (s zero)}}.

Elpi Query lp:{{bootstrap {{forall A : Prop, A \/ A -> A}}
                          J
                          (s zero)}}.

(* Example lemmas *)
Lemma example1 : forall A B: Prop, (A -> B) -> A -> B.
elpi coq_fpc 2.
Show Proof.
Qed.

(* Lemma example2 : forall A : Prop, A \/ A -> A.
Elpi Trace.
elpi coq_fpc 1.
Qed. *)

Lemma example3 : forall A B : Prop, A -> A \/ B.
elpi coq_fpc 1.
Qed.

Lemma example4 : forall A B : Prop, A -> B -> A /\ B.
elpi coq_fpc 1.
Qed.

Lemma example5 : forall A B : Prop, A /\ B -> A.
elpi coq_fpc 1.
Qed.

Lemma example6 : forall A : Type -> Prop, forall x : Type, (A x) -> (A x).
elpi coq_fpc 1.
Qed.

Lemma example7 : forall A : Type -> Prop, forall x, (A x) -> (exists x, (A x)). 
elpi coq_fpc 2.
Qed.

(*
  This query succeeds, even though the behaviour of disjunction elimination seems different from
the one specified in the fpc. Maybe some form of beta-conversion happens when doing quotations?
*)
Elpi Query lp:{{bootstrap {{forall A B : Prop, A /\ B -> A}}
     {{(fun (A B : Prop) (H : A /\ B) => and_ind (fun (H0 : A) (_ : B) => H0) H) }}
                          (s zero).}}.
(* Debug queries to check the behaviour on terms *)
(* Elpi Trace. *)
Elpi Query lp:{{
  check (coqcert (fun _ _ (x\ (fun _ _ (y\ app [x, y]))))) (async [] (unk (((n j) arr (n l)) arr (n j) arr (n l)))).
}}.
Elpi Query lp:{{bootstrap {{forall A : Prop, A -> A}} F.}}.
Elpi Query lp:{{ljf_entry (coqcert (fun _ _ (y\y))) ((n j) arr (n j)).}}.
Elpi Query lp:{{ljf_entry (coqcert (fun _ _ (x\ (fun _ _ (y\y)))))  ((n l) arr ((n j) arr (n j))).}}.
Elpi Query lp:{{ljf_entry ((coqcert X) <c> (dd (s (zero))))  (((n j) arr (n j))).}}.
Elpi Query lp:{{
  ljf_entry (coqcert {{(fun (A B : Prop) (H : A) (_ : B) => or_introl H)}}) (((n j) arr (n l)) arr ((n j) !+! (n l))).
}}.
Elpi Query lp:{{ljf_entry (coqcert (fun _ _ (x\ (fun _ _ (y\y)))))  ((n l) arr ((n j) arr (n j))).}}.
Elpi Query lp:{{ljf_entry ((coqcert X) <c> (dd (s (zero))))  (((n j) arr (n j))).}}.
Elpi Query lp:{{ljf_entry ((coqcert X) <c> (dd (s (zero))))  ((n l) arr ((n j) arr (n j))).}}.

Elpi Query lp:{{
  check (coqcert (fun _ _ (x\ (fun _ _ (y\ app [x, y]))))) (async [] (unk (((n j) arr (n l)) arr (n j) arr (n l)))).
}}.
Elpi Query lp:{{
  check (coqcert {{(lp:H: lp:A->lp:B) (lp:J: lp:B) => H J}}) (async [] (unk (((n j) arr (n l)) arr (n j) arr (n l)))).
}}.
Elpi Query lp:{{
  check (coqcert ({{(fun (A B : Prop) (H : A) (_ : B) => or_introl H)}}) (async [] (unk (((n j) arr (n l)) arr ((n j) or (n l)))))).
}}.
Elpi Query lp:{{
  check (coqcert (fun _ _ (x\x))) (async [] (unk (((n j) arr (n j)) arr (n j) arr (n j)))).
}}.

Elpi Query lp:{{bootstrap {{(forall A : Type -> Prop, forall x, (A x) -> (exists x, (A x)))}}
                          {{(fun (A : Type -> Prop) (x : Type) (H : A x) => ex_intro (fun x0 : Type => A x0) x H)}}
                          (s (s zero)).}}.

Elpi Query lp:{{bootstrap {{(forall A : Type -> Prop, forall x, (A x) -> (exists x, (A x)))}}
 J %                         {{(fun (A : Type -> Prop) (x : Type) (H : A x) => ex_intro (fun x0 : Type => A x0) x H)}}
                          (s (s zero)).}}.
