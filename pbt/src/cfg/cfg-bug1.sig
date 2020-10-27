sig cfg-bug1.
accum_sig kernel.
accum_sig cfg.
accum_sig cfg-ss-bug1.
accum_sig cfg-aa.
accum_sig cfg-bb.

% Tests
type   sound   cert -> lst ab -> nat -> nat -> o.
type   complete   cert -> lst ab -> nat  -> o.

type   b1s    lst ab -> nat -> nat -> o.
type   b1c    lst ab -> nat  -> o.

type   b1sr   lst ab -> nat -> nat -> o.
type   b1cr   lst ab -> nat  -> o.

type   qc   o.
