module pairing-fpc.

/* start */
% allC     (A <c> B) (x\ (C x) <c> (D' x))   :- allC     A C,
%                                               pi w\ (copyi T w) => copyc D (D' w),
%                                               allCx    B D T.

%allCx    (A <c> B) (x\ (C <c> (D x))) T    :- allCx  A C T, allC B D.

storeL_jc   (A <c> B) (L <c> D) (I <i> J)    :- storeL_jc   A L I,   storeL_jc   B D J.
decideL_je  (A <c> B) (C <c> D) (I <i> J)     :- decideL_je  A C I,     decideL_je  B D J.
releaseL_je (A <c> B) (C <c> D)               :- releaseL_je A C,       releaseL_je B D.
decideR_je (A <c> B) (C <c> D)               :- decideR_je A C,       decideR_je B D.
storeR_jc (A <c> B) (C <c> D)               :- storeR_jc A C,       storeR_jc B D.
releaseR_je (A <c> B) (C <c> D)               :- releaseR_je A C,       releaseR_je B D.
initialL_je (C <c> B)               :- initialL_je C,       initialL_je B.
initialR_je (C <c> B) (I <i> J)               :- initialR_je C I,       initialR_je B J.
andNeg_jc  (A <c> B) (C <c> D) (E <c> F)     :- andNeg_jc  A C E,     andNeg_jc  B D F.
or_jc  (A <c> B) (C <c> D) (E <c> F)     :- or_jc  A C E,     or_jc  B D F.
andPos_je  (A <c> B) (C <c> D) (E <c> F)     :- andPos_je  A C E,     andPos_je  B D F.
arr_je  (A <c> B) (C <c> D) (E <c> F)     :- arr_je  A C E,     arr_je  B D F.
or_je   (A <c> B) (C <c> D) E             :- or_je   A C E,     or_je   B D E.
andNeg_je   (A <c> B) (C <c> D) E             :- andNeg_je   A C E,     andNeg_je   B D E.
arr_jc    (A <c> B) (C <c> D)             :- arr_jc    A C,         arr_jc    B D.
andPos_jc    (A <c> B) (C <c> D)             :- andPos_jc    A C,         andPos_jc    B D.
true_jc    (A <c> B) (C <c> D)             :- true_jc    A C,         true_jc    B D.
true_je    (A <c> B)              :- true_je    A,         true_je    B.
cut_je     (A <c> B) (C <c> D) (E <c> F) Cut :- cut_je     A C E Cut, cut_je     B D F Cut.

some_je    (A <c> B) (C <c> D) W             :- some_je    A C W,     some_je    B D W.
all_je    (A <c> B) (C <c> D) W             :- all_je    A C W,     all_je    B D W.

% some_jc, all_jc               cert -> (i -> cert) -> prop.

/* end */
