module maximal-fpc.
/* start */
storeL_jc  (max N (maxi (ix N) A)) (max (succ N) A) (ix N).
decideL_je    (max N (maxi I A))   	 (max N A) I.
decideR_je (max N (max1 A))     	 (max N A).
storeR_jc (max N (max1 A))     	 (max N A).
releaseL_je (max N (max1 A))     	 (max N A).
releaseR_je  (max N (max1 A))     	 (max N A).
initialL_je   (max _N  max0).
initialR_je   (max _N (maxa I)) I.
cut_je    (max N (maxf F A B)) 	 (max N A) (max N B) F.
some_jc (max N (maxv C ))    	 (x\ max N (C x)).
all_jc  (max N (maxv C ))    	 (x\ max N (C x)).
some_je (max N (maxt T A))   	 (max N A) T.
all_je  (max N (maxt T A))   	 (max N A) T.
arr_jc (max N (max1 A))     	 (max N A).
andPos_jc (max N (max1 A))   	 (max N A).

or_jc (max N (max2 A B))   	 (max N A) (max N B).
andNeg_jc (max N (max2 A B))   	 (max N A) (max N B).
arr_je (max N (max2 A B))   	 (max N A) (max N B).
andPos_je  (max N (max2 A B))   	 (max N A) (max N B).

or_je (max N (maxc C A))   	 (max N A) C.
andNeg_je  (max N (maxc C A))   	 (max N A) C.

true_je   (max _N  max0).
true_jc  (max N (max1 A))     	 (max N A). 
/* end */
% When replaying: give a negative counter so that the store
% Does not use it.
% storeC   (max N (maxi I A)) (max N A) I :- N < 0.
