module harness.
accumulate kernel, fpcs.

% Two signature dependent predicate specifications
% Declaring what is a term and what is the subterm relationship.

tm a.
tm (f X)   :- tm X.
tm (g X Y) :- tm X, tm Y.

subtm T T.
subtm T (f S) :- subtm T S.
subtm T (g R S) :- subtm T R ; subtm T S.

prog (p X) (or (eq X a) (some Y\ (and (eq X (f Y)) (p Y)))).

% tjsim harness
% ?- check ((qheight 3) <c> (collect In []) <c> (rec Xi)) (p (f (f a))).

% The answer substitution:
% Xi = choose right (term (f a) (binary empty (choose right (term a (binary empty (choose left empty))))))
% In = f a :: a :: nil

interp tt.
interp (eq T T).
interp (and G1 G2) :- interp G1, interp G2.
interp (or G1 G2)  :- interp G1; interp G2.
interp (some G)    :- interp (G T).
interp A           :- prog A Body, interp Body.

prog (is_nat N) (or (eq N zero) (some M\ and (eq N (succ M)) (is_nat M))).

prog (is_natlist L) (or (eq L null) 
                        (some Hd\ some Tl\ (and (eq L (cons Hd Tl))
                                           (and (is_nat Hd) (is_natlist Tl))))).
prog (rev L K) (aux L K null).
prog (aux L K Acc) (or (and (eq L null) (eq K Acc)) 
                       (some Hd\ some Tl\ and (eq L (cons Hd Tl)) (aux Tl K (cons Hd Acc)))).

cexrev Gen Xs :- 
  check Gen (is_natlist Xs),
  interp (rev Xs Ys), not(Xs = Ys).

