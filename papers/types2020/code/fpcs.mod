module fpcs.
accumulate kernel.
/* resources */
ttE     (qheight _).
eqE     (qheight _).
orE     (qheight H) (qheight H) _.
someE   (qheight H) (qheight H) _.
andE    (qheight H) (qheight H) (qheight H).
unfoldE (qheight H) (qheight H') :- H  > 0, H' is H  - 1.

eqE     (qsize In In).
ttE     (qsize In In).
orE     (qsize In Out) (qsize In Out) _.
someE   (qsize In Out) (qsize In Out) _.
andE    (qsize In Out) (qsize In Mid) (qsize Mid Out).
unfoldE (qsize In Out) (qsize In' Out) :-
                                       In > 0, In' is In - 1.
/* end */
/* max */
ttE     (max empty).
eqE     (max empty).
orE     (max (choose C M)) (max M) C.
someE   (max (term   T M)) (max M) T.
andE    (max (binary M N)) (max M) (max N).
unfoldE (max M) (max M).
/* end */
/* pairing */
ttE     (A <c> B) :- ttE A, ttE B.
eqE     (A <c> B) :- eqE A, eqE B.
someE   (A <c> B) (C <c> D) T   :- someE A C T, someE B D T.
orE     (A <c> B) (C <c> D) E   :- orE A C E, orE B D E. 
unfoldE (A <c> B) (C <c> D)     :- unfoldE A C, unfoldE B D.
andE    (A <c> B) (C <c> D) (E <c> F) :-
                                      andE A C E, andE B D F. 
/* end */

eqE   (l-or-r In In).
ttE   (l-or-r In In).
orE   (l-or-r [C|In] Out)
      (l-or-r In Out) C.
someE (l-or-r In Out) (l-or-r In Out) _.
andE  (l-or-r In Out) (l-or-r In Mid)
                      (l-or-r Mid Out).
unfoldE (l-or-r In Out) (l-or-r In Out).

/* collect */
eqE   (collect In In).
ttE   (collect In In).
orE   (collect In Out)
      (collect In Out) C.
andE  (collect In Out) (collect In Mid)
                       (collect Mid Out).
unfoldE (collect In Out) (collect In Out).
someE (collect [(c_nat T) |In] Out)
      (collect In Out) (T : nat).
someE (collect [(c_list_nat T)|In] Out)
      (collect In Out) (T : list nat).

subterm Item Item.
subterm Item (c_nat (succ M)) :- 
  subterm Item (c_nat M).
subterm Item (c_list_nat (Nat::L)) :- 
  subterm Item (c_nat Nat) ;
  subterm Item (c_list_nat L).
/* end */
/* huniv */
ttE     (huniv _).
eqE     (huniv _).
orE     (huniv Pred) (huniv Pred) _.
andE    (huniv Pred) (huniv Pred) 
                     (huniv Pred).
unfoldE (huniv Pred) (huniv Pred).
someE (huniv Pred) (huniv Pred) 
      (T:nat) :- Pred (c_nat T).
someE (huniv Pred) (huniv Pred) 
      (T:list nat) :- Pred (c_list_nat T).
/* end */
