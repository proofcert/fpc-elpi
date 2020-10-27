module stlc-bug4.
accumulate kernel.
accumulate stlc.
accumulate stlc-tcc-bug4.
accumulate stlc-wt.
accumulate stlc-value.
accumulate stlc-step.
accumulate stlc-tests.
accumulate nat.
accumulate lst.
accumulate fpc-qbound.
accumulate fpc-pair.

prog (is_cnt plus) (tt).
%prog (tcc plus (funTy intTy (funTy intTy intTy))) (tt).

prog (is_value (app (c plus) V)) (is_value V).

prog (step (app (app (c plus) X) Y) Z) (and (is_value X) (and (is_value Y) (add_value X Y Z))).
prog (add_value (c (toInt zero)) (c X) (c X)) (tt).
prog (add_value (c (toInt (succ X))) (c Y) (c (toInt (succ Z)))) (add_value (c (toInt X)) (c Y) (c (toInt Z))).

% Tests (prog)

% With the default ratio (2), the test succeeds at height 7: 76.743.
% Using the bounds directly (7, 14): 57.492 (so recomputation is not too bad).
% Direct bounds (6, 14): 22.096.
% Direct bounds (5, 14): 2.956 (this is the minimum).
% What is happening here is that the ratio takes us too deep too fast.
