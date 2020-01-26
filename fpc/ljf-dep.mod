% This modified kernel introduces an eigenvariable with the implication introduction
% module ljf-dep.
accumulate spy.

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
type check        cert -> seq -> term -> prop.  % top-level predicate
type abs               (term -> term) -> term.  % Handle abstractions during proof reconstruction
% isNegAtm (n _).
% isPosAtm (p _).
%    & isNegForm t-.
%   & isNegForm (d- _).

isNegForm {{lp:_ /\ lp:_}} & isNegForm {{lp:_ -> lp:_}}.
isNegForm (prod _ _ _).
isNeg A :- isNegForm A ; isNegAtm A.

isPosForm {{lp:_ \/ lp:_}}.
% isPosForm (d+ _)    & isPosForm (some _)  & isPosForm f  &  isPosForm t+.
isPos A :- isPosForm A.

pred_type (sort prop).
pred_type (prod _ (sort (typ _)) (x\ Ty2)) :- pred_type Ty2.

:if "DEBUG" check A B T :- announce (check A B T).
ljf_entry Cert Form Term :- check Cert (async [] (unk Form)) Term.

% Structural Rules
% decide
  % decideL_je (coqcert Hd) (coqabs (x\ x)) (idxoftm Hd).
  % decideL_je (coqcert {{and_ind lp:T lp:Idx}}) (coqabs (x\ {{and_ind lp:T lp:x}})) (idxoftm Idx).
  % decideL_je (coqcert (app [Hd,B])) (coqabs (x\ app [x,B])) (idxoftm Hd).
check Cert (async [] (str R)) Var :- decideL_je Cert Cert' Indx,
  storage Indx Var N, coq.say "Choosing" Indx N, isNeg N,
  check Cert' (lfoc N R) (abs (x\ x)).
check Cert (async [] (str R)) (app [Var,B]) :- decideL_je Cert Cert' Indx,
  storage Indx Var N, coq.say "Choosing" Indx N, isNeg N, 
  check Cert' (lfoc N R) (abs (x\ app [x,B])).
check Cert (async [] (str R)) {{and_ind lp:T lp:Var}} :- decideL_je Cert Cert' Indx,
  storage Indx Var N, coq.say "Choosing" Indx N, isNeg N, 
  check Cert' (lfoc N R) (abs (x\ {{and_ind lp:T lp:x}})).
check Cert (async [] (str P)) T :-
  isPos P, decideR_je Cert Cert', check Cert' (rfoc P) T.
% release
check Cert (lfoc P R) T :- isPos P, releaseL_je Cert Cert', check Cert' (async [P] (str R)) T.
check Cert (rfoc N)   T :- isNeg N, releaseR_je Cert Cert', check Cert' (async [] (unk N))  T.
% store
check Cert (async [C|Theta] R) (abs T) :- (isNeg C ; isPosAtm C), coq.say "no",
  storeL_jc Cert Cert' Indx, 
  pi w\ storage (Indx w) w C => %coq.say "Storing" C "at" (Indx w),
    check (Cert' w) (async Theta R) (T w).
check Cert (async [] (unk D)) T :- (isPos D ; isNegAtm D),
  storeR_jc Cert Cert', check Cert' (async [] (str D)) T.

% Identity rules
% initial (all atoms are negative)
check Cert (lfoc Na Na) T :- isNegAtm Na, initialL_je Cert.
% check Cert (rfoc Pa)    T :- isPosAtm Pa, initialR_je Cert Indx, storage Indx Pa.
% cut
% check Cert (async [] (str R)) :- cut_je Cert CertA CertB F, 
%   check CertA (async [] (unk F)), check CertB (async [F] (str R)).

% Asynchronous Rules
%% Product
% Non dependent: then it is an implication
check Cert (async [] (unk (prod _ Ty1 (x\ Ty2)))) (fun _name Ty1 F) :-
  arr_jc Cert Cert',
  check Cert' (async [Ty1] (unk Ty2)) (abs F).
% Dependent: if the abstracted type is type -> (type -> (... -> prop)) it's a pred var
check Cert (async [] (unk (prod _ Ty1 Ty2))) (fun _name Ty1 F) :-
  pred_type Ty1,
  pi w\ isNegAtm w => check Cert (async [] (unk (Ty2 w))) (F w).
% Dependent: if abstraction is over (type) and there is an all_jc, then it's a forall-right
check Cert (async [] (unk (prod _ (sort (typ _)) Ty2))) (fun _name Ty1 F) :-
  all_jc Cert Cert',
  pi t\ check (Cert' t) (async [] (unk (Ty2 t))) (F t).
%% Disjunction
check Cert (async [{{lp:A \/ lp:B}}| Theta] R) (abs (x\ app [global OrInd, A, B, _, fun _ A T1, fun _ B T2, x])):-
  coq.locate "or_ind" OrInd,
  or_jc Cert CertA CertB,
  check CertA (async [A | Theta] R) (abs T1),
  check CertB (async [B | Theta] R) (abs T2).
% conjunction
% check Cert (async [(A &+& B )| Theta] R) :- andPos_jc Cert Cert',
%   check Cert' (async [A , B | Theta] R).
check Cert (async [] (unk {{lp:A /\ lp:B}})) {{conj lp:T1 lp:T2}} :-
  andNeg_jc Cert CertA CertB,
  check CertA (async [] (unk A)) T1, check CertB (async [] (unk B)) T2.
% quantifers
% check Cert (async [some B | Theta] R) :- some_jc Cert Cert',
%   pi w\ check (Cert' w) (async [B w | Theta] R).
% Units
% check _Cert (async [] (unk t-)).
% check _Cert (async [f | _Theta] _R).
% check Cert (async [t+| Theta] R) :- true_jc Cert Cert', check Cert' (async Theta R).
% % Delays
% check Cert (async [d+ A|Theta] R)   :- check Cert (async [A|Theta] R).
% check Cert (async [] (unk (d- R))) :- check Cert (async [] (unk R)).

% Synchronous Rules
% arrow (non dependent)
check Cert (lfoc {{lp:A -> lp:B}} R) (abs (x\ app [x,T])) :-
  arr_je Cert CertA CertB,
  check CertA (rfoc A) T, check CertB (lfoc B R) (abs (x\ x)).
% Forall (dependent, can only depend on type)
check Cert (lfoc (prod _ (sort (typ _)) B) R) (abs (x\ app [x, T])):-
  all_je Cert Cert' Tm, check Cert' (lfoc (B Tm) R) T.
% disjunction
check Cert (rfoc {{lp:A \/ lp:B}}) T :- or_je Cert Cert' Choice, 
  ((Choice = left, T={{or_introl lp:T'}}, check Cert' (rfoc A) T');
   (Choice = right, T={{or_intror lp:T'}}, check Cert' (rfoc B) T')).
% conjunction
% check Cert (rfoc (A &+& B)) :- andPos_je Cert CertA CertB,
%    check CertA (rfoc A), check CertB (rfoc B).
check Cert (lfoc {{lp:A /\ lp:B}} R) (abs T):-
  andNeg_je Cert Cert' Choice,
  ((Choice = left,  check Cert' (lfoc A R) (abs (x\ T {{proj1 lp:x}})));
   (Choice = right, check Cert' (lfoc B R) (abs (x\ T {{proj2 lp:x}})))).
% quantifers
check Cert (rfoc (ex Type B)) {{ex_intro lp:Pred lp:T lp:Proof}} :-
  some_je Cert Cert' T, check Cert' (rfoc (B T)) Proof.
% % Units
% check Cert (rfoc t+) :- true_je Cert.
% % Delays
% check Cert (rfoc (d+ A))            :- check Cert (rfoc A). 
% check Cert (lfoc (d- A) R)          :- check Cert (lfoc A R) .
