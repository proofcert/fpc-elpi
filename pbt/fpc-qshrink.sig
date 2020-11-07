sig fpc-qshrink.
accum_sig kernel.

% Term shrinkers
type   shrink    A -> A -> o.

% A shrinker FPC
type   qshrink    A -> cert -> cert.
type   qcompute   cert.

% The companion witness extractor and converter
type   qsubst    cert -> cert.
type   qsubst1   A -> cert -> cert.
type   qsubst0   cert.

type   subst2shrink cert -> cert -> o.
