sig fpc-qrandom.
accum_sig kernel.

% Helpers
type   member   A -> list A -> o.

% A randomized "quick"-style FPC
kind   qweight   type.
type   qw        string -> int -> qweight.

type   qtries    int -> list qweight -> cert.
type   qrandom   list qweight -> cert.

type   sum_weights     list nprolog -> list qweight -> int -> list qweight -> o.
type   select_clause   int -> list qweight -> string -> o.
