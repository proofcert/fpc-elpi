sig stlc-subexp.
accum_sig kernel.
accum_sig stlc.
accum_sig stlc-wt.
accum_sig stlc-value.
accum_sig stlc-step.

% Tests
type   is_pexp      lst exp -> exp -> prolog. %
type   cexsexp   exp -> exp -> ty -> o.
type   unty    exp ->  o.
type   divrg    exp ->  o.
%type   cexpres   exp -> exp -> ty -> o.
