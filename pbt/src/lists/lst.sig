sig lst.
accum_sig nat.
accum_sig kernel.
accum_sig fpc-qshrink.

kind   lst          type -> type.
type   null         lst A.
type   cons         A -> lst A -> lst A.

type   is_natlist   lst nat -> prolog.
type   ord          lst nat -> prolog.
type   ord_bad      lst nat -> prolog.
type   ins          nat -> lst nat -> lst nat -> prolog.
type   append       lst A -> lst A -> lst A -> prolog.
type   rev          lst A -> lst A -> prolog.
