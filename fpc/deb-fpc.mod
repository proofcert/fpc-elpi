module deb-fpc.

% The FPC for the deb certificate format (using De Bruijn nameless dummies)

arr_jc      (lc C (lambda D)) (lc C D).
storeR_jc   (lc C D) (lc C D).
releaseR_je (lc C D) (lc C D).
storeL_jc   (lc C D) (x\ lc C' D) (x\ idx C) :- C' is C + 1.
decideL_je  (lc C (apply H A)) (args C A) (idx V) :- V is C - H - 1.
initialL_je (args C []).
arr_je      (args C (A::As)) (lc C A) (args C As).

storeR_jc   (lc C D) (lc C D).
decideR_je  (lc C D) (lc C D).
% storeR_jc   (lc C (lambda D)) (lc C (lambda D)).
% decideR_je  (lc C (lambda D)) (lc C (lambda D)).
% andPos_je   (lc C (lambda D)) (lc C D) (lc C (lambda D)).
true_je     (lc C D).
