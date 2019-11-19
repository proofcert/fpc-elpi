%% The first part of this file is the old stlc-examples file
%% Examples from the stlc fpc are then translated to maxcerts and sent to Coq
%% For the coq-elpi interaction, scroll down

%% Begin: stlc-examples

module coq-fpc.
accumulate control.
accumulate ljf-formulas, iforms, ljf-polarize.
accumulate ljf-kernel.
accumulate stlc-fpc.
accumulate pairing-fpc.
accumulate maximal-fpc.
% accumulate coq-maximal-fpc.

% Convert standard lambda-tree syntactic representation to a
% deBruijn-style encoding.  Two recursive predicates are used.
debi C (lam R) E :- C' is C + 1, pi x\ vr C x => debi C' (R x) E.
debi C M (apply H (Args [])) :- debe C M H Args.
% The use of "functional difference lists" here is to avoid
% using a separate call to reverse later.
debe C (app M N) H ZZ :- debi C N N', debe C M H Args, ZZ = (x\ Args (N'::x)).
debe C H D (x\x) :- vr K H, D is C - K - 1.

of (app M N) A       :- of M (B imp A), of N B.
of (lam R) (A imp B) :- pi x\ of x A => of (R x) B.

example 1 (lam x\x) (i imp i).
example 2 (lam x\ lam y\ y) (j imp (i imp i)).
example 3 (lam x\ lam y\ app x y) ((i imp j) imp (i imp j)).
example 4 (lam x\ lam y\ lam z\ app z (app z x)) (i imp (j imp ((i imp i) imp i))).
example 5 (lam x\ lam y\ app y (lam z\ app z x)) (i imp ((((i imp j) imp j) imp k) imp k)).
example 6 (lam x\ lam y\ app y (lam z\ app z x)) (j imp ((((i imp j) imp j) imp k) imp k)).

test_all :- 
   example X Tm Ty, debi 0 Tm Deb, polarize- Ty Form, 
   (sigma Str\ term_to_string X Str, coq.say Str, coq.say " "),
   if (ljf_entry (lc 0 Deb) Form)
      (coq.say "Success\n") 
      (coq.say "Fail\n"), 
  fail.

hope I :- example I Tm Ty, debi 0 Tm Deb, polarize- Ty Form, ljf_entry (lc 0 Deb) Form.

%% End: stlc-examples

%% Begin coq-elpi interaction

pred maximize i:int, o:cert.
maximize I M :- example I Tm Ty, debi 0 Tm Deb, polarize- Ty Form, ljf_entry ((lc 0 Deb) <c> M) Form.

pred nat->coq i:nat, o:term.
nat->coq zero {{0}}.
nat->coq (succ X) {{S lp:N}} :- nat->coq X N.
pred max->coq i:max, o:term.
max->coq max0 {{C0}}.
max->coq (max1 X) {{C1 lp:C}} :- max->coq X C.
max->coq (max2 X Y) {{C2 lp:C lp:D}} :- max->coq X C, max->coq Y D.
max->coq (maxa (ix N)) {{Cx lp:CN}} :- nat->coq N CN.
max->coq (maxi (ix N) C) {{Cd lp:CN lp:D}} :- nat->coq N CN, max->coq C D.

