% DM I'm in the process of editing this so that it might look more
% compact if we plan to insert any of it the paper.  Probably there
% is not enough room but it helps me to understand the code if I
% revise it.

% Thoughts: drop Ctx for lP contexts; drop check for three
% predicates (one for each phase async, lfoc, rfoc).

accum_sig ljf-lambda-certificates.
accumulate tools.

type isNegForm, isNegAtm, isPosForm, isPosAtm, isNeg, isPos     term -> prop. 
type ljf_entry      cert -> term -> term -> prop.

kind rhs                                 type.  % The RHS of the async sequent
type str                          term -> rhs.  % The right-hand-side is stored.
type unk                          term -> rhs.  % The right-hand-side is unknown.
type una                (term -> term) -> rhs.  % The right-hand-side is open.

kind seq                                 type.  % sequents
type async           list term -> rhs  -> seq.  % async
type lfoc                 term -> term -> seq.  % left focus
type rfoc                         term -> seq.  % right focus
type storage    index -> term -> term -> prop.  % storage of formulas
type check      list (pair term term) -> cert -> seq -> term -> prop.  % top-level predicate
type abs               (term -> term) -> term.  % Handle abstractions during proof reconstruction
type look                list (pair A B) -> A -> B -> prop.

look [pr X Y|_] X Y.
look [_|LS]       X Y :- look LS X Y.

isNegForm {{lp:_ /\ lp:_}} & isNegForm {{lp:_ -> lp:_}}.
isNegForm (prod _ _ _).
isNegAtm (app [Hd|_Rest]) :- isNegAtm Hd.
isNeg A :- isNegForm A ; isNegAtm A.

isPosForm {{lp:_ \/ lp:_}}.
isPosForm {{False}}.
isPosForm (app [global Ex_indt, _, _]) :- coq.locate "ex" Ex_indt.
isPos A :- isPosForm A; isPosAtm A.

type term_type term -> prop.
type pred_type term -> list term -> prop.

pred_type (sort prop) [].
pred_type (prod _ TermType (x\ Ty2)) [TermType|Rest]:- pred_type Ty2 Rest.

ljf_entry C Form Term :- check [] C (async [] (unk Form)) Term.

check Ctx C (async [C|Th] R) (abs T) :- (isNeg C ; isPosAtm C), storeL_jc C C' Indx, pi w\ decl w _Name C =>    check [(pr w C)|Ctx] (C' w) (async Th R) (T w).
check Ctx C (async [] (str P)) T :- isPos P, decideR_je C C', check Ctx C' (rfoc P) T.
check Ctx C (async [] (str R)) Term :- decideL_je C C' Indx, look Ctx Var N, isNeg N, check Ctx C' (lfoc N R) (abs T), Term = (T Var).
check Ctx C (async [] (unk (prod Name Ty1 Ty2))) (fun Name Ty1 F) :- pred_type Ty1 Args, mkproplist Args term_type Preds, pi w\ isNegAtm w => decl w Name Ty1 => Preds => check Ctx C (async [] (unk (Ty2 w))) (F w).
check Ctx C (async [] (unk (prod _ Ty1 (x\ Ty2)))) (fun _name Ty1 F) :- arr_jc C C', check Ctx C' (async [Ty1] (unk Ty2)) (abs F).
check Ctx C (async [] (unk (prod _ Ty1 Ty2))) (fun _name Ty1 F) :- not (pred_type Ty1 _), all_jc C C', pi t\ decl t _Name Ty1 => check Ctx (C' t) (async [] (unk (Ty2 t))) (F t).
check Ctx C (async [] (unk D)) T :- (isPos D ; isNegAtm D), storeR_jc C C', check Ctx C' (async [] (str D)) T.
check Ctx C (async [] (unk {{lp:A /\ lp:B}})) {{conj lp:T1 lp:T2}} :- andNeg_jc C CA CB, check Ctx CA (async [] (unk A)) T1, check Ctx CB (async [] (unk B)) T2.
check Ctx C (async [app [global Ex_indt, Ty, (fun _ Ty B)]|Th] R) (abs (x\ {{ex_ind lp:Fun lp:x}})) :- coq.locate "ex" Ex_indt, Fun = (fun _ Ty (x\ fun _ (B x) (Proof x))), some_jc C C', pi w\ decl w _Name Ty => check Ctx (C' w) (async [B w|Th] R) (abs (Proof w)).
check Ctx C (async [{{False}}|_Th] R) (abs (x\ app [global FalseInd, F, x])):- (R = unk F; R = str F), coq.locate "False_ind" FalseInd.
check Ctx C (async [{{lp:A \/ lp:B}}|Th] R) (abs (x\ app [global OrInd, A, B, F, fun _ A T1, fun _ B T2, x])) :- (R = unk F; R = str F), coq.locate "or_ind" OrInd, or_jc C CA CB, check Ctx CA (async [A|Th] R) (abs T1), check Ctx CB (async [B|Th] R) (abs T2).

check Ctx C (lfoc (prod _ Ty B) R) (abs (x\ T (app [x, Tm]))) :- term_type Ty, all_je C C' Tm, check Ctx C' (lfoc (B Tm) R) (abs T).
check Ctx C (lfoc Na Na) T :- T = (abs (x\ x)), isNegAtm Na, initialL_je C.
check Ctx C (lfoc P R) T :- isPos P, releaseL_je C C', check Ctx C' (async [P] (str R)) T.
check Ctx C (lfoc {{lp:A -> lp:B}} R) (abs (x\ T (app [x, Tm]))) :- arr_je C CA CB, check Ctx CA (rfoc A) Tm, check Ctx CB (lfoc B R) (abs T).
check Ctx C (lfoc {{lp:A /\ lp:B}} R) (abs T):- andNeg_je C C' Choice, ((Choice = left, check Ctx C' (lfoc A R) (abs U), T = (x\ U {{proj1 lp:x}})); (Choice = right, check Ctx C' (lfoc B R) (abs U), T = (x\ U {{proj2 lp:x}}))).

check Ctx C (rfoc (app [global Ex_indt, Ty, (fun _ Ty B)])) (app [global Ex_intro, Ty, (fun _ Ty B), T, Proof]) :- coq.locate "ex" Ex_indt, coq.locate "ex_intro" Ex_intro, some_je C C' T, check Ctx C' (rfoc (B T)) Proof.
check Ctx C (rfoc N) T :- isNeg N, releaseR_je C C', check Ctx C' (async [] (unk N))  T.
check Ctx C (rfoc Pa) Var :- isPosAtm Pa, initialR_je C Indx, look Ctx Var Pa.
check Ctx C (rfoc {{lp:A \/ lp:_B}}) {{or_introl lp:T}} :- or_je C C' left, check Ctx C' (rfoc A) T.
check Ctx C (rfoc {{lp:_A \/ lp:B}}) {{or_intror lp:T}} :- or_je C C' right, check Ctx C' (rfoc B) T.
