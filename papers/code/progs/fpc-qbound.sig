sig fpc-qbound.
accum_sig kernel.

% A "quick"-style FP
kind   qbound    type.
type   qheight   int -> qbound.
type   qsize     int -> int -> qbound.
type   qgen      qbound -> cert.

% An integer strict size (e.g., 4) becomes a range 4 .. 0, whose
% subtraction denotes exactly the size of a subterm to be generated.
type   qidsize    int -> qbound.
type   qidsize'   int -> int -> qbound.
type   qrgsize    int -> int -> qbound.

% Iterated and strict term heights.
type   qidheight    int -> qbound.
type   qidheight'   int -> int -> qbound.
type   qrgheight    int -> int -> qbound.
