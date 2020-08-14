module stlc-step-bug7.

prog (step (app (c hd) (app (app (c cns) X) XS)) X) (and (is_value X) (is_value XS)).
prog (step (app (c tl) (app (app (c cns) X) XS)) XS) (and (is_value X) (is_value XS)).
prog (step (app (lam M T) V) (M V)) (is_value V). % W = M V, dynamic pattern OK?
prog (step (app M1 M2) (app M1' M2)) (step M1 M1').
%prog (step (app V M2) (app V M2')) (and (is_value V) (step M2 M2')). % Bug 7
