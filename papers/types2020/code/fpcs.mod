module fpcs.
accumulate kernel.
/* resources */
ttE     (qheight _).
prodE   (qheight H) (qheight H) (qheight H).
unfoldE Kn (qheight H) (qheight H') K :-
      std.mem Kn K, H  > 0, H' is H  - 1.
% 
eqE     (qsize In In).
prodE  (qsize In Out) (qsize In Mid) (qsize Mid Out).
unfoldE Kn (qsize In Out) (qsize In' Out) K :-
   std.mem Kn K, In > 0, In' is In - 1.
%
ttE     (A <c> B) :- ttE A, ttE B.
unfoldE (A <c> B) (C <c> D) :- unfoldE A C, unfoldE B D.
prodE (pair C1 C2) (pair C1' C2') (pair C1'' C2'') :-
  prodE C1 C1' C1'', prodE C2 C2' C2''.

/* end */
% /* max */
% ttE     (max empty).
% eqE     (max empty).
% orE     (max (choose C M)) (max M) C.
% someE   (max (term   T M)) (max M) T.
% andE    (max (binary M N)) (max M) (max N).
% unfoldE (max M) (max M).
% /* end */

/* pairing */
ttE     (A <c> B) :- ttE A, ttE B.
unfoldE (A <c> B) (C <c> D)     :- unfoldE A C, unfoldE B D.
prodE (pair C1 C2) (pair C1' C2') (pair C1'' C2'') :-
	prodE C1 C1' C1'',
	prodE C2 C2' C2''.
/* end */

