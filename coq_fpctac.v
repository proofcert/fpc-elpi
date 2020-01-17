From elpi Require Import elpi.

(*Simply prints context and goal, doesn't solve anything *)
Elpi Tactic id.
Elpi Accumulate lp:{{
  solve _ [goal Ctx Ev Ty _] _ :-
    coq.say "goal" Ev "is\n" Ctx "\n-------\n" Ty.
}}. 

Elpi Db coq_fpc.db lp:{{
  type coqcert term -> cert.
  type coqabs  (term -> term) -> cert.
  type hold index -> (term -> term) -> cert.
  % type coqidx  term -> index. %% Not used anymore?
  type tmofidx index -> term.
  type idxoftm term -> index.
  pred prop_name o:term, o:iform.
  atomic X :- prop_name _ X.
  :if "DEBUG" coq_to_iform A B :- announce (coq_to_iform A B).
  coq_to_iform X Y :-
    prop_name X Y.
  coq_to_iform {{lp:X -> lp:Y}} (X' imp Y') :-
    coq_to_iform X X',
    coq_to_iform Y Y'.
  coq_to_iform {{lp:X \/ lp:Y}} (X' or Y') :-
    coq_to_iform X X',
    coq_to_iform Y Y'.
  type bootstrap term -> term -> nat -> prop.
  :if "DEBUG" bootstrap A B N :- announce (bootstrap A B N).
  bootstrap (prod _ (sort prop) Ty) (fun _ (sort prop) F) N:-
    pi x y z\ prop_name x y =>
      bootstrap (Ty x) (F z) N.
  bootstrap {{lp:T1 \/ lp:T2}} Term N :-
    coq_to_iform {{lp:T1 \/ lp:T2}} Form, coq.say Form,
    polarize- Form PForm, ljf_entry (<c> (dd N) (coqcert Term)) PForm.
  bootstrap {{lp:T1 -> lp:T2}} Term N :-
    coq_to_iform {{lp:T1 -> lp:T2}} Form,
    polarize- Form PForm, ljf_entry (<c> (dd N) (coqcert Term)) PForm.
  arr_jc (coqcert (fun _name _type F)) (coqabs F).
  arr_je (coqabs (x\ app [x,T])) (coqcert T) (coqabs (x\ x)).
  % arr_je (coqabs (x\ x)) (coqcert A) (coqcert (tmofidx Idx)).
  pred assoc o:index, o:term.
  storeL_jc (coqabs T) (x\ coqcert (T x)) (x\ idxoftm x). % :- assoc Idx T.
  decideL_je (coqcert (app [Hd,B])) (coqabs (x\ app [x,B])) (idxoftm Hd). % :- assoc Idx Hd.
  decideL_je (coqcert Hd) (coqabs (x\ x)) (idxoftm Hd). % :- assoc Idx Tm.
  initialL_je _.
  storeR_jc Cert Cert.
  releaseR_je Cert Cert.
  %% New additions for connectives
  decideR_je Cert Cert.
  or_je (coqcert {{or_introl lp:T}}) (coqcert T) left.
  or_je (coqcert {{or_intror lp:T}}) (coqcert T) right.
  % or_jc (coqabs (x\ app [global (const «or_ind» ), _, _, _, (fun _ _ T1), (fun _ _ T2), x])) (coqabs T1) (coqabs T1).
  or_jc (coqabs (x\ {{or_ind (fun H0 : lp:_ => lp:T1) (fun H0 : lp:_ => lp:T2) lp:x}})) (coqabs T1) (coqabs T1).
  solve [(int N)] [goal Ctx Ev Ty _] [] :- 
    int_to_nat N Nat,
    bootstrap Ty Ev Nat.
}}.

Elpi Tactic coq_fpc.
Elpi Accumulate File "fpc/ljf-polarize.mod".
Elpi Accumulate File "fpc/ljf-lambda.mod".
(* Elpi Accumulate File "fpc/stlc-fpc.mod". *)
Elpi Accumulate File "fpc/pairing-fpc.mod".
Elpi Accumulate File "fpc/dd-fpc.mod".
Elpi Accumulate Db coq_fpc.db.
Elpi Typecheck.

Elpi Debug "DEBUG".
(* Elpi Trace. *)
Elpi Query lp:{{bootstrap {{forall A B : Prop, A \/ A -> A}}
                          {{(fun (A _ : Prop) (H : A \/ A) => or_ind (fun H0 : A => H0) (fun H0 : A => H0) H)}}
                          (s zero)}}.

Elpi Query lp:{{bootstrap {{forall A B : Prop, A \/ A -> A}}
                          {{(fun (A _ : Prop) (H : A \/ A) => or_ind (fun H0 : A => H0) (fun H0 : A => H0) H)}}
                          (s zero)}}.

Lemma example2 : forall A B : Prop, A \/ A -> A.
elpi coq_fpc 1.
Elpi Query lp:{{int_to_nat 1 X.}}.
Lemma example1 : forall A B: Prop, (A -> B) -> A -> B.
elpi coq_fpc 2.
Qed.

Lemma example3 : forall A B : Prop, A -> A \/ B.
elpi coq_fpc 1.
Show Proof.

Elpi Query lp:{{
  check (coqcert (fun _ _ (x\ (fun _ _ (y\ app [x, y]))))) (async [] (unk (((n j) arr (n l)) arr (n j) arr (n l)))).
}}.
Show Proof.
Qed.
Elpi Query lp:{{coq.say {{lp:A \/ lp:B}}.}}.

(* Elpi Trace. *)
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
Elpi Query lp:{{ljf_entry (dd (s (s (s (zero)))))  ((n l) arr ((n j) arr (n j))).}}.
Elpi Query lp:{{bootstrap {{forall A B : Prop, A -> (A->B) -> B}} Tm F.}}.

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

