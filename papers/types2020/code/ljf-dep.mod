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

type ljf_entry   cert -> term -> term -> prop.

kind rhs                                 type.  % The RHS of the async sequent
type str                          term -> rhs.  % The right-hand-side is stored.
type unk                          term -> rhs.  % The right-hand-side is unknown.
type una                (term -> term) -> rhs.  % The right-hand-side is open.

type async           list term -> rhs  -> cert -> term -> prop.  % async
type lfoc                 term -> term -> cert -> term -> prop.  % left focus
type rfoc                         term -> cert -> term -> prop.  % right focus
type abs               (term -> term) -> term.  % Handle abstractions during proof reconstruction

type term_type term -> prop.  % Where is this defined?
type pred_type term -> list term -> prop.

pred_type (sort prop) [].
pred_type (prod _ TermType (x\ Ty2)) [TermType|Rest]:- pred_type Ty2 Rest.

type assoc   term -> term -> prop.


% :if "DEBUG" check A B T :- coq.say "check" A B T, fail.
% ljf_entry Cert Form Term :- check (async [] (unk Form)) Cert Term.

ljf_entry C Form Term :- async [] (unk Form) C Term.

async [] (str R) Cert Term :- decideE Cert Cert' Indx, assoc Var N, isNeg N,
  lfoc N R Cert' (abs T), Term = (T Var).
async [] (str P) Cert T :- isPos P, decideR_je Cert Cert', rfoc P Cert' T.
lfoc P R Cert T :- isPos P, releaseL_je Cert Cert', async [P] (str R) Cert' T.
rfoc N Cert   T :- isNeg N, releaseR_je Cert Cert', async [] (unk N) Cert'  T.
async [C|Theta] R Cert (abs T) :- (isNeg C ; isPosAtm C),
  storeC Cert Cert' Indx, pi w\ decl w _Name C => assoc w C =>  async Theta R (Cert' w) (T w).
async [] (unk D) Cert T :- (isPos D ; isNegAtm D),
  storeR_jc Cert Cert', async [] (str D) Cert' T.
lfoc Na Na Cert (abs (x\ x)) :- isNegAtm Na, initialE Cert.
rfoc Pa Cert    Var :- isPosAtm Pa, initialR_je Cert Indx, assoc Var Pa.

async [] (unk (prod _ Ty1 (x\ Ty2))) Cert (fun _name Ty1 F) :-
  impC Cert Cert', async [Ty1] (unk Ty2) Cert' (abs F).
async [] (unk (prod Name Ty1 Ty2)) Cert (fun Name Ty1 F) :-
  pred_type Ty1 Args, mkproplist Args term_type Preds,
  pi w\ isNegAtm w => decl w Name Ty1 => Preds => async [] (unk (Ty2 w)) Cert (F w).
async [] (unk (prod _ Ty1 Ty2)) Cert (fun _name Ty1 F) :-
  not (pred_type Ty1 _),  all_jc Cert Cert',
  pi t\ decl t _Name Ty1 => async [] (unk (Ty2 t)) (Cert' t) (F t).
async [{{lp:A \/ lp:B}}| Theta] R Cert (abs (x\ app [global OrInd, A, B, F, fun _ A T1, fun _ B T2, x])):-
  (R = unk F; R = str F), coq.locate "or_ind" OrInd, or_jc Cert CertA CertB,
  async [A | Theta] R CertA (abs T1),
  async [B | Theta] R CertB (abs T2).
async [{{False}}| _Theta] R Cert (abs (x\ app [global FalseInd, F, x])):-
  (R = unk F; R = str F), coq.locate "False_ind" FalseInd.
async [] (unk {{lp:A /\ lp:B}}) Cert {{conj lp:T1 lp:T2}} :-
  andNeg_jc Cert CertA CertB, async [] (unk A) CertA T1, async [] (unk B) CertB T2.
async [app [global Ex_indt, Ty, (fun _ Ty B)] | Theta] R Cert
               (abs (x\ {{ex_ind lp:Fun lp:x}})) :-
  coq.locate "ex" Ex_indt,
  Fun = (fun _ Ty (x\ fun _ (B x) (Proof x))),
  some_jc Cert Cert',
  pi w\ decl w _Name Ty => async [B w | Theta] R (Cert' w) (abs (Proof w)).

lfoc {{lp:A -> lp:B}} R Cert (abs (x\ T (app [x, Tm]))) :- impE Cert CertA CertB, rfoc A CertA Tm, lfoc B R CertB (abs T).
lfoc (prod _ Ty B) R Cert (abs (x\ T (app [x, Tm]))) :- term_type Ty, all_je Cert Cert' Tm, lfoc (B Tm) R Cert' (abs T).
rfoc {{lp:A \/ lp:_B}} Cert {{or_introl lp:T}} :- or_je Cert Cert' left,  rfoc A Cert' T.
rfoc {{lp:_A \/ lp:B}} Cert {{or_intror lp:T}} :- or_je Cert Cert' right, rfoc B Cert' T.
lfoc {{lp:A /\ lp:B}} R Cert (abs T):- andNeg_je Cert Cert' Choice,
  ((Choice = left,  lfoc A R Cert' (abs U), T = (x\ U {{proj1 lp:x}}));
   (Choice = right, lfoc B R Cert' (abs U), T = (x\ U {{proj2 lp:x}}))).
rfoc (app [global Ex_indt, Ty, (fun _ Ty B)]) Cert
               (app [global Ex_intro, Ty, (fun _ Ty B), T, Proof]) :-
  coq.locate "ex" Ex_indt, coq.locate "ex_intro" Ex_intro,
  some_je Cert Cert' T, rfoc (B T) Cert' Proof.
