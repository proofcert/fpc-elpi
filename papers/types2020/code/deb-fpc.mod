% Version of official code copied here and edited for possible inclusion in the paper
% The FPC for the deb certificate format (using De Bruijn nameless dummies)

module deb-fpc.

/* start */
arr_jc       (lc C (lambda D)) (lc C D).
arr_je       (args C (A::As)) (lc C A) (args C As).
initialL_je (args C []).
decideL_je   (lc C (apply H A)) (args C A) (idx V) :- V is C - H - 1.
storeL_jc    (lc C D) (x\ lc C' D) (x\ idx C) :- C' is C + 1.
storeR_jc    (lc C D) (lc C D).
releaseR_je  (lc C D) (lc C D).
/* end */

decideR_je  (lc C D) (lc C D).
true_je     (lc C D).

% storeR_jc   (lc C (lambda D)) (lc C (lambda D)).
% decideR_je  (lc C (lambda D)) (lc C (lambda D)).
% andPos_je   (lc C (lambda D)) (lc C D) (lc C (lambda D)).
