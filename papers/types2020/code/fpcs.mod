module fpcs.
accumulate kernel.
/* resources */
ttE   (qheight _).
sortE (qheight _).
prodE (qheight H) (qheight H) (qheight H).
decideE Kn (qheight H) (qheight H') K :- std.mem Kn K, H  > 0, H' is H  - 1.

ttE   (qsize In In).
sortE (qsize In In).
prodE (qsize In Out) (qsize In Mid) (qsize Mid Out).
decideE Kn (qsize In Out) (qsize In' Out) K :- std.mem Kn K, In > 0, In' is In - 1.

ttE   (A <c> B) :- ttE A,   ttE B.
sortE (A <c> B) :- sortE A, sortE B.
prodE (C1 <c> C2) (D1 <c> D2) (E1 <c> E2) :- prodE C1 D1 E1, prodE C2 D2 E2.
decideE Kn (A <c> B) (C <c> D) K :- decideE Kn A C K, decideE Kn B D K.
/* end */
% /* max */
% ttqE     (max empty).
% eqE     (max empty).
% orE     (max (choose C M)) (max M) C.
% someE   (max (term   T M)) (max M) T.
% andE    (max (binary M N)) (max M) (max N).
% decideE (max M) (max M).
% /* end */

/* pairing */
ttE     (A <c> B) :- ttE A, ttE B.
decideE (A <c> B) (C <c> D)     :- decideE A C, decideE B D.
prodE (pair C1 C2) (pair D1 D2) (pair E1 E2) :-	prodE C1 D1 E1,	prodE C2 D2 E2.
/* end */

