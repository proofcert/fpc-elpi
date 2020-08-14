sig nat.
accum_sig kernel.
accum_sig fpc-qshrink.

kind   nat      type.
type   zero     nat.
type   succ     nat -> nat.

type   is_nat   nat -> prolog.

type   leq      nat -> nat -> prolog.
type   gt       nat -> nat -> prolog.
