module deb-fpc.
accumulate control.
accumulate ljf-formulas, iforms, ljf-polarize.

% The FPC for the deb certificate format (using De Bruijn nameless dummies)

arr_jc      (lc C D) (lc C D).
storeR_jc   (lc C D) (lc C D).
releaseR_je (lc C D) (lc C D).
storeL_jc   (lc C D) (lc C' D) (idx C) :- C' is C + 1.
decideL_je  (lc C (apply H A)) (args C A) (idx V) :- V is C - H - 1.
initialL_je (args C []).
arr_je      (args C (A::As)) (lc C A) (args C As).

storeR_jc   (lc C (lambda D)) (lc C (lambda D)).
decideR_je  (lc C (lambda D)) (lc C (lambda D)).
andPos_je   (lc C (lambda D)) (lc C D) (lc C (lambda D)).
true_je     (lc C D).

% Some utilities 

% Convert standard lambda-tree syntactic representation to a
% deBruijn-style encoding.  Two recursive predicates are used.
debi C (lam R) (lambda E) :- C' is C + 1, pi x\ var C x => debi C' (R x) E.
debi C M (apply H (Args [])) :- debe C M H Args.
% The use of "functional difference lists" here is to avoid
% using a separate call to reverse later.
debe C (app M N) H ZZ :- debi C N N', debe C M H Args, ZZ = (x\ Args (N'::x)).
debe C H D (x\x) :- var K H, D is C - K - 1.

of (app M N) A       :- of M (B imp A), of N B.
of (lam R) (A imp B) :- pi x\ of x A => of (R x) B.

example 1 (lam x\x) (i imp i).
example 2 (lam x\ lam y\ y) (j imp (i imp i)).
example 3 (lam x\ lam y\ app x y) ((i imp j) imp (i imp j)).
example 4 (lam x\ lam y\ lam z\ app z (app z x)) (i imp (j imp ((i imp i) imp i))).
example 5 (lam x\ lam y\ app y (lam z\ app z x)) (i imp ((((i imp j) imp j) imp k) imp k)).
example 6 (lam x\ lam y\ app y (lam z\ app z x)) (j imp ((((i imp j) imp j) imp k) imp k)).
example 7 (lam x\ lam y\ app y (lam z\ x))       (j imp ((((i imp j) imp j) imp k) imp k)).

% The following works with the kernal in the JAR paper:
% repo/parsifal/papers/fpc/journal/code/rev/ljf-kernel.mod

hope I :- example I Tm Ty, debi 0 Tm Deb, polarizeP Ty Form, ljf_entry (lc 0 Deb) Form.

test_all :- 
   example X Tm Ty, debi 0 Tm Deb, polarizeP Ty Form, 
   (sigma Str\ term_to_string X Str, print Str, print " "),
   if (ljf_entry (lc 0 Deb) Form)
      (print "Success\n") 
      (print "Fail\n"), 
  fail.
