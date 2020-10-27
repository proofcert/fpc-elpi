sig cfg.
accum_sig kernel.

kind   ab     type.
type   a, b   ab.

type   is_ab       ab -> prolog.
type   is_ablist   lst ab -> prolog.

type   ss, aa, bb   lst ab -> prolog.

type   neq     ab -> ab -> prolog.
type   count   ab -> lst ab -> nat -> prolog.
type   append       lst A -> lst A -> lst A -> prolog.