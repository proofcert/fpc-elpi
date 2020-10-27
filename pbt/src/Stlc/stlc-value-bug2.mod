module stlc-value-bug2.

% Bug 2
prog (is_value (c _)) (tt).
prog (is_value (lam _ _)) (tt).
prog (is_value (app (c cns) V)) (is_value V).
%prog (is_value (app (app (c cns) V1) V2)) (and (is_value V1) (is_value V2)).
