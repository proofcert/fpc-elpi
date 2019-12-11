module ljf-polarize.

polarize tt t+  &  polarize tt t-.
polarize ff f.
polarize (B and C) (B' &-& C') :- polarize B B', polarize C C'.
polarize (B and C) (B' &+& C') :- polarize B B', polarize C C'.
polarize (B or  C) (B' !+! C') :- polarize B B', polarize C C'.
polarize (B imp C) (B' arr C') :- polarize B B', polarize C C'.
polarize (forall B)(all B')  :- pi x\ polarize (B x) (B' x).
polarize (exists B)(some B') :- pi x\ polarize (B x) (B' x).
polarize A (n A) :- atomic A, polarize_neg A.
polarize A (p A) :- atomic A, polarize_pos A.

polarize+ A          (p A)     :- atomic A.
polarize+ (T imp S)  (A arr B) :- polarize+ T A, polarize+ S B.
polarize+ (forall T) (all B)   :- pi x\ polarize+ (T x) (B x).

polarize- A (n A) :- atomic A.
polarize- (T imp S) (A arr B) :- polarize- T A, polarize- S B.

polarizeP A (n A) :- atomic A.
polarizeN A (n A) :- atomic A.
polarizeP (T imp S) ((A arr B) &+& t+) :- polarizeN T A, polarizeP S B.
polarizeN (T imp S) (A arr B)          :- polarizeP T A, polarizeN S B.
