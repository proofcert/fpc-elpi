sig fpc-rec.
accum_sig kernel.

% Traces and trace certificates
kind   trace   type.
type   tend    trace.
type   tseq    string -> trace -> trace.
type   tand    trace -> trace -> trace.

type   rec     trace -> cert.

% Pretty-printing
type   app     list A -> list A -> list A -> o.
type   pp      trace -> list string -> o.
