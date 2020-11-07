% Version of official code copied here and edited for possible inclusion in the paper
type dd     nat -> cert.
type indx   index.
kind nat    type.
type zero   nat.
type s      nat -> nat.
storeC   (dd D) (x\ dd D) (x\ indx).
decideE  (dd (s D)) (dd D) indx.
decideR_je  (dd (s D)) (dd D).
storeR_jc   (dd D) (dd D).
releaseL_je (dd D) (dd D).
releaseR_je (dd D) (dd D).
initialE (dd _D).
initialR_je (dd _D) indx.
some_jc     (dd D) (x\ dd D).
all_jc      (dd D) (x\ dd D).
some_je     (dd D) (dd D) _.
all_je      (dd D) (dd D) _.
impC      (dd D) (dd D).
andPos_jc    (dd D) (dd D).
or_jc       (dd D) (dd D) (dd D).
andNeg_jc   (dd D) (dd D) (dd D).
impE      (dd D) (dd D) (dd D).
andPos_je   (dd D) (dd D) (dd D).
or_je       (dd D) (dd D) _.
andNeg_je   (dd D) (dd D) _.
true_je    (dd _D).
true_jc    (dd D) (dd D).

pred int_to_nat i:int, o:nat.
int_to_nat 0 zero.
int_to_nat I (s N) :- I' is (I - 1), int_to_nat I' N.