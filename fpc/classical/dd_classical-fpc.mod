type dd     int -> cert.
type indx   index.
kind nat    type.
all_kc      (dd D) (x\ dd D).
andNeg_kc   (dd D) (dd D) (dd D).
andPos_ke   (dd D) (dd D) (dd D).
% cut_ke      (dd D) (dd D) Form.
decide_ke   (dd N) (dd N') indx :- N' is N - 1.
false_kc    (dd D) (dd D).
initial_ke  (dd _D) indx.
orNeg_kc    (dd D) (dd D).
orPos_ke    (dd D) (dd D) _Choice.
release_ke  (dd D) (dd D).
some_ke     (dd D) (dd D) _Term.
store_kc    (dd D) (x\ dd D) (x\ indx).
true_ke     (dd _D).

pred int_to_nat i:int, o:nat.
int_to_nat 0 zero.
int_to_nat I (s N) :- I' is (I - 1), int_to_nat I' N.