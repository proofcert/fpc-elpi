% DM I'm in the process of editing this so that it might look more
% compact if we plan to insert any of it the paper.  Probably there
% is not enough room but it helps me to understand the code if I
% revise it.

% Thoughts: drop check for three predicates (one for each phase async, lfoc, rfoc).

% First steps: Dropped Ctx in exchange for lP contexts.  Added assoc predicate instead.

accum_sig ljf-lambda-certificates.
accumulate tools.

type isNegForm, isNegAtm, isPosForm, isPosAtm, isNeg, isPos     term -> prop.

isNegForm {{lp:_ /\ lp:_}} & isNegForm {{lp:_ -> lp:_}}.
isNegForm (prod _ _ _).
isNegAtm (app [Hd|_Rest]) :- isNegAtm Hd.
isNeg A :- isNegForm A ; isNegAtm A.

isPosForm {{lp:_ \/ lp:_}}.
isPosForm {{False}}.
isPosForm (app [global Ex_indt, _, _]) :- coq.locate "ex" Ex_indt.
isPos A :- isPosForm A; isPosAtm A.

type ljf_entry      cert -> term -> term -> prop.

kind rhs                                 type.  % The RHS of the async sequent
type str                          term -> rhs.  % The right-hand-side is stored.
type unk                          term -> rhs.  % The right-hand-side is unknown.
type una                (term -> term) -> rhs.  % The right-hand-side is open.

kind seq                                 type.  % sequents
type async           list term -> rhs  -> seq.  % async
type lfoc                 term -> term -> seq.  % left focus
type rfoc                         term -> seq.  % right focus
type abs               (term -> term) -> term.  % Handle abstractions during proof reconstruction

type term_type term -> prop.  % Where is this defined?
type pred_type term -> list term -> prop.

pred_type (sort prop) [].
pred_type (prod _ TermType (x\ Ty2)) [TermType|Rest]:- pred_type Ty2 Rest.

type check      cert -> seq -> term -> prop.  % top-level predicate
type assoc   term -> term -> prop.

ljf_entry C Form Term :- check C (async [] (unk Form)) Term.

:if "DEBUG" check A B T :- coq.say "check" A B T, fail.
ljf_entry Cert Form Term :- check Cert (async [] (unk Form)) Term.

check Cert (async [] (str R)) Term :-
  decideE Cert Cert' Indx,
  assoc Var N, isNeg N,
  check Cert' (lfoc N R) (abs T),
  Term = (T Var).
check Cert (async [] (str P)) T :-
  isPos P, decideR_je Cert Cert', check Cert' (rfoc P) T.
check Cert (lfoc P R) T :- isPos P, releaseL_je Cert Cert', check Cert' (async [P] (str R)) T.
check Cert (rfoc N)   T :- isNeg N, releaseR_je Cert Cert', check Cert' (async [] (unk N))  T.
check Cert (async [C|Theta] R) (abs T) :- (isNeg C ; isPosAtm C),
  storeC Cert Cert' Indx, 
  pi w\ decl w _Name C => assoc w C =>  check (Cert' w) (async Theta R) (T w).
check Cert (async [] (unk D)) T :- (isPos D ; isNegAtm D),
  storeR_jc Cert Cert', check Cert' (async [] (str D)) T.
check Cert (lfoc Na Na) T :- T = (abs (x\ x)), isNegAtm Na, initialE Cert.
check Cert (rfoc Pa)    Var :- isPosAtm Pa, initialR_je Cert Indx, assoc Var Pa.

check Cert (async [] (unk (prod _ Ty1 (x\ Ty2)))) (fun _name Ty1 F) :-
  impC Cert Cert',
  check Cert' (async [Ty1] (unk Ty2)) (abs F).
check Cert (async [] (unk (prod Name Ty1 Ty2))) (fun Name Ty1 F) :-
  pred_type Ty1 Args, mkproplist Args term_type Preds,
  pi w\ isNegAtm w => decl w Name Ty1 => Preds => check Cert (async [] (unk (Ty2 w))) (F w).
check Cert (async [] (unk (prod _ Ty1 Ty2))) (fun _name Ty1 F) :-
  not (pred_type Ty1 _),
  all_jc Cert Cert',
  pi t\ decl t _Name Ty1 => check (Cert' t) (async [] (unk (Ty2 t))) (F t).
check Cert (async [{{lp:A \/ lp:B}}| Theta] R) (abs (x\ app [global OrInd, A, B, F, fun _ A T1, fun _ B T2, x])):-
  (R = unk F; R = str F),
  coq.locate "or_ind" OrInd,
  or_jc Cert CertA CertB,
  check CertA (async [A | Theta] R) (abs T1),
  check CertB (async [B | Theta] R) (abs T2).
check Cert (async [{{False}}| _Theta] R) (abs (x\ app [global FalseInd, F, x])):-
  (R = unk F; R = str F),
  coq.locate "False_ind" FalseInd.
check Cert (async [] (unk {{lp:A /\ lp:B}})) {{conj lp:T1 lp:T2}} :-
  andNeg_jc Cert CertA CertB,
  check CertA (async [] (unk A)) T1, check CertB (async [] (unk B)) T2.
check Cert (async [app [global Ex_indt, Ty, (fun _ Ty B)] | Theta] R)
               (abs (x\ {{ex_ind lp:Fun lp:x}})) :-
  coq.locate "ex" Ex_indt,
  Fun = (fun _ Ty (x\ fun _ (B x) (Proof x))),
  some_jc Cert Cert',
  pi w\ decl w _Name Ty => check (Cert' w) (async [B w | Theta] R) (abs (Proof w)).

check Cert (lfoc {{lp:A -> lp:B}} R) (abs (x\ T (app [x, Tm]))) :-
  impE Cert CertA CertB,
  check CertA (rfoc A) Tm, check CertB (lfoc B R) (abs T).
check Cert (lfoc (prod _ Ty B) R) (abs (x\ T (app [x, Tm]))) :-
  term_type Ty,
  all_je Cert Cert' Tm, check Cert' (lfoc (B Tm) R) (abs T).
check Cert (rfoc {{lp:A \/ lp:_B}}) {{or_introl lp:T}} :- or_je Cert Cert' left, 
  check Cert' (rfoc A) T.
check Cert (rfoc {{lp:_A \/ lp:B}}) {{or_intror lp:T}} :- or_je Cert Cert' right, 
  check Cert' (rfoc B) T.
check Cert (lfoc {{lp:A /\ lp:B}} R) (abs T):-
  andNeg_je Cert Cert' Choice,
  ((Choice = left,  check Cert' (lfoc A R) (abs U), T = (x\ U {{proj1 lp:x}}));
   (Choice = right, check Cert' (lfoc B R) (abs U), T = (x\ U {{proj2 lp:x}}))).
check Cert (rfoc (app [global Ex_indt, Ty, (fun _ Ty B)]))
               (app [global Ex_intro, Ty, (fun _ Ty B), T, Proof]) :-
  coq.locate "ex" Ex_indt,
  coq.locate "ex_intro" Ex_intro,
  some_je Cert Cert' T, check Cert' (rfoc (B T)) Proof.
