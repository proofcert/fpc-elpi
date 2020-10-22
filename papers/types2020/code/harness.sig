sig harness.
accum_sig kernel, fpcs.

% A specific first-order signature follows

kind i   type.

type p   i -> oo.
type q   i -> i -> oo.

type a   i.
type f   i -> i.
type g   i -> i -> i.

type tm          i -> o.
type subtm  i -> i -> o.

type   interp    oo -> o.
type   np        string -> oo -> oo.
type   prog      oo -> oo -> o.

% A sample program
kind   nat      type.
type   zero     nat.
type   succ     nat -> nat.

type   is_nat   nat -> oo.
type   leq      nat -> nat -> oo.
type   gt       nat -> nat -> oo.
type   is_natlist   lst nat -> oo.

kind   lst          type -> type.
type   null         lst A.
type   cons         A -> lst A -> lst A.

type cexrev     cert -> lst nat -> o.
type rev        lst nat -> lst nat -> oo.
type aux        lst nat -> lst nat -> lst nat -> oo.

