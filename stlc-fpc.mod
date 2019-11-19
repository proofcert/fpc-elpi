module stlc-fpc.

/* start */
arr_jc      (lc C D) (lc C D).
storeR_jc   (lc C D) (lc C D).
releaseR_je (lc C D) (lc C D).
storeL_jc   (lc C D) (lc C' D) (idx C) :- C' is C + 1.
decideL_je  (lc C (apply H A)) (args C A) (idx V) :- V is C - H - 1.
initialL_je (args _C []).
arr_je      (args C (A::As)) (lc C A) (args C As).
/* end */
