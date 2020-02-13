% This modified kernel introduces an eigenvariable with the implication introduction
% module ljf-dep.
% accumulate spy.
accum_sig ljf-lambda-certificates.

type isNegForm, isNegAtm, isPosForm, isPosAtm, isNeg, isPos     term -> prop. 
type ljf_entry      cert -> term -> term -> prop.

%  The following should be hidden in the .mod file.

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
% isNegAtm (n _).
% isPosAtm (p _).
%    & isNegForm t-.
%   & isNegForm (d- _).
type look list (pair A B) -> A -> B -> prop.
look [pr X Y|_] X Y.
look [_|LS]       X Y :- look LS X Y.
isNegForm {{lp:_ /\ lp:_}} & isNegForm {{lp:_ -> lp:_}}.
isNegForm (prod _ _ _).
isNegAtm (app [Hd|_Rest]) :- isNegAtm Hd.
isNeg A :- isNegForm A ; isNegAtm A.

isPosForm {{lp:_ \/ lp:_}}.
% isPosForm (d+ _)    & isPosForm (some _)  & isPosForm f  &  isPosForm t+.
isPos A :- isPosForm A.

type pred_type term -> prop.
pred_type (sort prop).
pred_type (prod _ _ (x\ Ty2)) :- pred_type Ty2.

:if "DEBUG" check Ctx A B T :- coq.say "check" Ctx A B T, fail.
ljf_entry Cert Form Term :- check [] Cert (async [] (unk Form)) Term.

% Structural Rules
% decide
  % decideL_je (coqcert Hd) (coqabs (x\ x)) (idxoftm Hd).
  % decideL_je (coqcert {{and_ind lp:T lp:Idx}}) (coqabs (x\ {{and_ind lp:T lp:x}})) (idxoftm Idx).
  % decideL_je (coqcert (app [Hd,B])) (coqabs (x\ app [x,B])) (idxoftm Hd).
check Ctx Cert (async [] (str R)) (T Var) :- coq.say "Deciding...", decideL_je Cert Cert' Indx, coq.say "Cert",
  % sigma A B C\ storage A B C, coq.say "Choosing" Indx N, isNeg N,
  look Ctx Var N, coq.say "Choosing" N "at" Var,
  check Ctx Cert' (lfoc N R) (abs T).
% check Ctx Cert (async [] (str R)) (app [Var,B]) :- decideL_je Cert Cert' Indx,
%   storage Indx Var N, coq.say "Choosing" Indx N, isNeg N, 
%   check Ctx Cert' (lfoc N R) (abs (x\ app [x,B])).
% check Ctx Cert (async [] (str R)) {{and_ind lp:T lp:Var}} :- decideL_je Cert Cert' Indx,
%   storage Indx Var N, coq.say "Choosing" Indx N, isNeg N, 
%   check Ctx Cert' (lfoc N R) (abs (x\ {{and_ind lp:T lp:x}})).
check Ctx Cert (async [] (str P)) T :-
  isPos P, decideR_je Cert Cert', check Ctx Cert' (rfoc P) T.
% release
check Ctx Cert (lfoc P R) T :- isPos P, releaseL_je Cert Cert', check Ctx Cert' (async [P] (str R)) T.
check Ctx Cert (rfoc N)   T :- isNeg N, releaseR_je Cert Cert', check Ctx Cert' (async [] (unk N))  T.
% store
check Ctx Cert (async [C|Theta] R) (abs T) :- (isNeg C ; isPosAtm C),
  storeL_jc Cert Cert' Indx, 
  % pi w\ storage indx w C => coq.say "Storing" C "at" (Indx w),
  pi w\ coq.say "Storing" C "at" w,
    check [(pr w C)| Ctx] (Cert' w) (async Theta R) (T w).
check Ctx Cert (async [] (unk D)) T :- (isPos D ; isNegAtm D),
  storeR_jc Cert Cert', check Ctx Cert' (async [] (str D)) T.
% Identity rules
% initial (all atoms are negative)
check Ctx Cert (lfoc Na Na) T :- coq.say "At neg" T, T = (abs (x\ x)), isNegAtm Na, initialL_je Cert.
% check Ctx Cert (rfoc Pa)    T :- isPosAtm Pa, initialR_je Cert Indx, storage Indx Pa.
% cut
% check Ctx Cert (async [] (str R)) :- cut_je Cert CertA CertB F, 
%   check Ctx CertA (async [] (unk F)), check Ctx CertB (async [F] (str R)).

% Asynchronous Rules
%% Product
% Non dependent: then it is an implication
check Ctx Cert (async [] (unk (prod _ Ty1 (x\ Ty2)))) (fun _name Ty1 F) :-
  arr_jc Cert Cert',
  check Ctx Cert' (async [Ty1] (unk Ty2)) (abs F).
% Dependent: if the abstracted type is type -> (type -> (... -> prop)) it's a pred var
check Ctx Cert (async [] (unk (prod _ Ty1 Ty2))) (fun _name Ty1 F) :-
  pred_type Ty1,
  pi w\ isNegAtm w => check Ctx Cert (async [] (unk (Ty2 w))) (F w).
% Dependent: if abstraction is over (type) and there is an all_jc, then it's a forall-right
check Ctx Cert (async [] (unk (prod _ Ty1 Ty2))) (fun _name Ty1 F) :-
  not (pred_type Ty1),
  all_jc Cert Cert',
  pi t\ check Ctx (Cert' t) (async [] (unk (Ty2 t))) (F t).
%% Disjunction
check Ctx Cert (async [{{lp:A \/ lp:B}}| Theta] R) (abs (x\ app [global OrInd, A, B, _, fun _ A T1, fun _ B T2, x])):-
  coq.locate "or_ind" OrInd,
  or_jc Cert CertA CertB,
  check Ctx CertA (async [A | Theta] R) (abs T1),
  check Ctx CertB (async [B | Theta] R) (abs T2).
% conjunction
% check Ctx Cert (async [(A &+& B )| Theta] R) :- andPos_jc Cert Cert',
%   check Ctx Cert' (async [A , B | Theta] R).
check Ctx Cert (async [] (unk {{lp:A /\ lp:B}})) {{conj lp:T1 lp:T2}} :-
  andNeg_jc Cert CertA CertB,
  check Ctx CertA (async [] (unk A)) T1, check Ctx CertB (async [] (unk B)) T2.
% quantifers
% check Ctx Cert (async [some B | Theta] R) :- some_jc Cert Cert',
%   pi w\ check Ctx (Cert' w) (async [B w | Theta] R).
% Units
% check Ctx _Cert (async [] (unk t-)).
% check Ctx _Cert (async [f | _Theta] _R).
% check Ctx Cert (async [t+| Theta] R) :- true_jc Cert Cert', check Ctx Cert' (async Theta R).
% % Delays
% check Ctx Cert (async [d+ A|Theta] R)   :- check Ctx Cert (async [A|Theta] R).
% check Ctx Cert (async [] (unk (d- R))) :- check Ctx Cert (async [] (unk R)).

% Synchronous Rules
% arrow (non dependent)
check Ctx Cert (lfoc {{lp:A -> lp:B}} R) (abs (x\ U (app [x, T]))) :-
  arr_je Cert CertA CertB,
  check Ctx CertA (rfoc A) T, check Ctx CertB (lfoc B R) (abs U).
% Forall (dependent, can only depend on type)
check Ctx Cert (lfoc (prod _ _ B) R) (abs (x\ T (app [x, Tm]))):-
  all_je Cert Cert' Tm, check Ctx Cert' (lfoc (B Tm) R) (abs T).
% disjunction
check Ctx Cert (rfoc {{lp:A \/ lp:B}}) T :- or_je Cert Cert' Choice, 
  ((Choice = left, T={{or_introl lp:T'}}, check Ctx Cert' (rfoc A) T');
   (Choice = right, T={{or_intror lp:T'}}, check Ctx Cert' (rfoc B) T')).
% conjunction
% check Ctx Cert (rfoc (A &+& B)) :- andPos_je Cert CertA CertB,
%    check Ctx CertA (rfoc A), check Ctx CertB (rfoc B).
check Ctx Cert (lfoc {{lp:A /\ lp:B}} R) (abs T):-
  andNeg_je Cert Cert' Choice,
  ((Choice = left,  check Ctx Cert' (lfoc A R) (abs U), T = (x\ U {{proj1 lp:x}}));
   (Choice = right, check Ctx Cert' (lfoc B R) (abs U), T = (x\ U {{proj2 lp:x}}))).
% quantifers
check Ctx Cert (rfoc (ex Type B)) {{ex_intro lp:Pred lp:T lp:Proof}} :-
  some_je Cert Cert' T, check Ctx Cert' (rfoc (B T)) Proof.
% % Units
% check Ctx Cert (rfoc t+) :- true_je Cert.
% % Delays
% check Ctx Cert (rfoc (d+ A))            :- check Ctx Cert (rfoc A). 
% check Ctx Cert (lfoc (d- A) R)          :- check Ctx Cert (lfoc A R) .
