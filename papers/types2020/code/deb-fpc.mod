% Version of official code copied here and edited for possible inclusion in the paper
% The FPC for the deb certificate format (using De Bruijn nameless dummies)

module deb-fpc.

/* start */
impC       (lc C (lambda D)) (lc C D).
impE       (args C (A::As)) (lc C A) (args C As).
initialE   (args C []).
decideE    (lc C (apply H A)) (args C A) (idx V) :- V is C - H - 1.
storeC     (lc C D) (x\ lc C' D) (x\ idx C) :- C' is C + 1.
/* end */
% DM Let's not show the following lines since they are not
%    relevant when all atoms are negative.
storeR_jc    (lc C D) (lc C D).
releaseR_je  (lc C D) (lc C D).

decideR_je  (lc C D) (lc C D).
true_je     (lc C D).

% storeR_jc   (lc C (lambda D)) (lc C (lambda D)).
% decideR_je  (lc C (lambda D)) (lc C (lambda D)).
% andPos_je   (lc C (lambda D)) (lc C D) (lc C (lambda D)).
