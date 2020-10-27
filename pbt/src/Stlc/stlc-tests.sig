sig stlc-tests.
accum_sig kernel.
accum_sig stlc.
accum_sig fpc-qbound.
accum_sig fpc-pair.
% Certificate generation

type   itsearch_h    cert -> o.
type   itsearch_s    cert -> o.
type   itsearch_hs   cert -> o.

% Test templates

type   cexprog   cert -> exp -> ty -> o.
type   cexpres   cert -> exp -> exp -> ty -> o.

% Concrete iterated tests

type   cexprog_h    exp -> ty -> o.
type   cexprog_s    exp -> ty -> o.
type   cexprog_hs   exp -> ty -> o.

type   cexpres_h    exp -> exp -> ty -> o.
type   cexpres_s    exp -> exp -> ty -> o.
type   cexpres_hs   exp -> exp -> ty -> o.
