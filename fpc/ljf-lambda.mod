% This modified kernel introduces an eigenvariable with the implication introduction
% This is achieved by changing storeL_jc to introduce an eigenvariable 
% and allowing the index (use for storage) to incorporate that eigenvariable.
module ljf-kernel.
accumulate spy.

type isNegForm, isNegAtm, isPosForm, isPosAtm, isNeg, isPos     form -> prop. 

isNegAtm (n _).
isPosAtm (p _).

isNegForm (_ &-& _) & isNegForm (_ arr _).
isNegForm (all _)   & isNegForm (d- _)    & isNegForm t-.
isNeg A :- isNegForm A ; isNegAtm A.

isPosForm (_ !+! _) & isPosForm (_ &+& _).
isPosForm (d+ _)    & isPosForm (some _)  & isPosForm f  &  isPosForm t+.
isPos A :- isPosForm A ; isPosAtm A.

% :if "DEBUG"
check A B :- announce (check A B).
ljf_entry Cert Form :- check Cert (async [] (unk Form)).

% :if "DEBUG" check A B :- spy (check A B).
% Structural Rules
% decide
check Cert (async [] (str R)) :- decideL_je Cert Cert' Indx,
  storage Indx N, isNeg N,
  check Cert' (lfoc N R).
check Cert (async [] (str P)) :-
  isPos P, decideR_je Cert Cert', check Cert' (rfoc P).
% release
check Cert (lfoc P R) :- isPos P, releaseL_je Cert Cert', check Cert' (async [P] (str R)).
check Cert (rfoc N)   :- isNeg N, releaseR_je Cert Cert', check Cert' (async [] (unk N)).
% store
check Cert (async [C|Theta] R) :- (isNeg C ; isPosAtm C),
  storeL_jc Cert Cert' Indx, 
  pi w\ storage (Indx w) C => check (Cert' w) (async Theta R).
check Cert (async [] (unk D)) :- (isPos D ; isNegAtm D),
  storeR_jc Cert Cert', check Cert' (async [] (str D)).

% Identity rules
% initial
check Cert (lfoc Na Na) :- isNegAtm Na, initialL_je Cert.
check Cert (rfoc Pa)    :- isPosAtm Pa, initialR_je Cert Indx, storage Indx Pa.
% cut
check Cert (async [] (str R)) :- cut_je Cert CertA CertB F, 
  check CertA (async [] (unk F)), check CertB (async [F] (str R)).

% Asynchronous Rules
% arrow
check Cert (async [] (unk (A arr B))) :-
  arr_jc Cert Cert', check Cert' (async [A] (unk B)).
% disjunction
check Cert (async [(A !+! B)| Theta] R) :- or_jc Cert CertA CertB,
  check CertA (async [A | Theta] R), check CertB (async [B | Theta] R).
% conjunction
check Cert  (async [(A &+& B )| Theta] R) :- andPos_jc Cert Cert',
  check Cert' (async [A , B | Theta] R).
check Cert (async [] (unk (A &-& B))) :- andNeg_jc Cert CertA CertB,
  check CertA (async [] (unk A)), check CertB (async [] (unk B)).
% quantifers
check Cert (async [some B | Theta] R) :- some_jc Cert Cert',
  pi w\ check (Cert' w) (async [B w | Theta] R).
check Cert (async [] (unk (all B))) :- all_jc Cert Cert',
  pi w\ check (Cert' w) (async [] (unk (B w))).
% Units
check _Cert (async [] (unk t-)).
check _Cert (async [f | _Theta] _R).
check Cert (async [t+| Theta] R) :- true_jc Cert Cert', check Cert' (async Theta R).
% Delays
check Cert (async [d+ A|Theta] R)   :- check Cert (async [A|Theta] R).
check Cert (async [] (unk (d- R))) :- check Cert (async [] (unk R)).

% Synchronous Rules
% arrow
check Cert (lfoc (A arr B) R) :- arr_je Cert CertA CertB,
  check CertA (rfoc A), check CertB (lfoc B R).
% disjunction
check Cert (rfoc (A !+! B)) :- or_je Cert Cert' Choice, 
  ((Choice = left,  check Cert' (rfoc A)); (Choice = right, check Cert' (rfoc B))).
% conjunction
check Cert (rfoc (A &+& B)) :- andPos_je Cert CertA CertB,
   check CertA (rfoc A), check CertB (rfoc B).
check Cert (lfoc (A &-& B) R) :- andNeg_je Cert Cert' Choice,
   ((Choice = left,  check Cert' (lfoc A R));
    (Choice = right, check Cert' (lfoc B R))).
% quantifers
check Cert (rfoc (some B)) :- some_je Cert Cert' T, check Cert' (rfoc (B T)).
check Cert (lfoc (all B) R) :- all_je Cert Cert' T, check Cert' (lfoc (B T) R).
% Units
check Cert (rfoc t+) :- true_je Cert.
% Delays
check Cert (rfoc (d+ A))            :- check Cert (rfoc A). 
check Cert (lfoc (d- A) R)          :- check Cert (lfoc A R) .
