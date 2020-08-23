module lkf-hosted.
accumulate "../ljf-dep".

type trans+, trans-   term -> term -> o.

lkf_entry Cert CForm Term :- trans- CForm IForm, coq.say IForm, ljf_entry Cert {{lp:IForm -> lp:fatom}} Term.

% trans- A B :- coq.say "trans-" A B, fail.
% trans+ A B :- coq.say "trans+" A B, fail.
nnf {{True}} {{True}}.
nnf {{False}} {{False}}.
nnf {{lp:A /\ lp:B}} {{lp:A' /\ lp:B'}} :- nnf A A', nnf B B'.
nnf {{lp:B \/ lp:C}} :- nnf A A', nnf B B'.
nnf A A :- atomic A, nnf_neg A.
nnf {{lp:B -> lp:C}} D :- not (C = {{False}}), nnf {{(lp:B -> False) \/ lp:C}} D.
nnf {{forall}} (forall B) (all B')   &
nnf (exists B) (some B')  :- pi x\ nnf (B x) (B' x).

nnf {{True -> False}} {{False}}.
nnf {{}}
nnf (neg (B and C)) (B' !-! C') &
nnf (neg (B and C)) (B' !+! C') &
nnf (neg (B or  C)) (B' &-& C') &
nnf (neg (B or  C)) (B' &+& C') :- nnf (neg B) B', nnf (neg C) C'.
nnf (neg (forall B)) (some B')   &
nnf (neg (exists B)) (all  B')   :- pi x\ nnf (neg (B x)) (B' x).
nnf (neg (neg B)) C     :- nnf B C.
nnf (neg A) (p A)       :- atomic A, nnf_neg A.
nnf (neg A) (n A)       :- atomic A, nnf_pos A.
nnf (neg (B imp C))   D :- nnf (neg ((neg B) or C)) D.
nnf (neg (B equiv C)) D :- nnf (neg ((B imp C) and (C imp B))) D.

trans+ {{False}} {{False}}.
trans+ {{True}}  {{True}}.
% trans+ (p A)     (p A).
trans+ {{lp:A \/ lp:B}} {{lp:A' \/  lp:B'}} :- trans+ A A', trans+ B B'. 
trans+ {{lp:A /\ lp:B}} {{lp:A' /\ lp:B'}}  :- trans+ A A', trans+ B B'.
trans+ (app [global Ex, Ty, (fun _ Ty B)]) (app [global Ex, Ty, (fun _ Ty B')]) :-
  coq.locate "ex" Ex,
  pi x\ trans+ (B x) (B' x).
trans+ N         {{lp:N' -> lp:fatom}} :-  isNeg N, trans- N N'.

trans- (prod Name Ty B) (prod Name Ty B') :-
  pred_type Ty Args, mkproplist Args term_type Preds,
  pi w\ isNegAtm w => decl w Name Ty => Preds => trans- (B w) (B' w).
trans- {{False}} {{True}}.
trans- {{True}}  {{False}}.
% trans- (n A)      (p A).
trans- Atm Atm :- isNegAtm Atm.
trans- P          {{lp:P' -> lp:fatom}}  :- isPos P, trans+ P P'.
trans- {{lp:A \/ lp:B}}  {{lp:A' /\ lp:B'}} :- trans- A A', trans- B B'. 
trans- {{lp:A /\ lp:B}}  {{lp:A' \/ lp:B'}} :- trans- A A', trans- B B'.
trans- {{lp:A -> lp:B}}  F :- trans+ {{(lp:A -> False) \/ lp:B}} F.
trans- (prod _ Ty B) (app [global Ex, Ty, (fun _ Ty B')])   :-
  not (pred_type Ty _),
  coq.locate "ex" Ex,
  pi x\ trans- (B x) (B' x).

% Now define the intuitionistic versions of the clecks and experts
% to simply call the classical versions.
andPos_jc   C C'        :- orNeg_kc   C C'.
andPos_je   C C' C''    :- andPos_ke  C C' C''.
decideL_je  C C' I      :- decide_ke  C C' I.
initialR_je C I         :- initial_ke C I.
or_jc       C C' C''    :- andNeg_kc  C C' C''.
or_je       C C' Choice :- orPos_ke   C C' Choice.
releaseR_je C C'        :- release_ke C C'.
some_jc     C C'        :- all_kc     C C' .
some_je     C C' T      :- some_ke    C C' T.
storeL_jc   C C' I      :- store_kc   C C' I.
true_jc     C C'        :- false_kc   C C'.
true_je     C           :- true_ke    C.
arr_jc      C C.
storeR_jc   C C.
arr_je      C C  fcert.
initialL_je fcert.
  % Missing in Zak's implementation
% releaseL_je fcert fcert.

%cut_je cert -> form -> cert -> cert -> o.
% cut_je C C1 C2 F :- cut_ke C C1 C2 N, isNeg N, negate N P, trans- P F.
% cut_je C C2 C1 F :- cut_ke C C1 C2 P, isPos P,             trans- P F.

% Notice we're using it in reverse : a lot better and safer to actually write a reversed version

%There is no initialL_je, each decide on the left is on the arrow, the arrow
% Is always followed by a false, the false is always released and the proof
% ends not with initial but with the false rule

% only release on the left if focus in on false

%No decideR_je since we only have "false" stored on the right.
% The only formula to store on the right is f ?



