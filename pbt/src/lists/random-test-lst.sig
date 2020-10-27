sig random-test-lst.
accum_sig nat.
accum_sig lst.

type   tries   int -> o.
type   check_ord_bad   nat -> lst nat -> cert -> o.
type   cex_ord_bad   nat -> lst nat -> o.
type   cex_ord_bad_shrink   nat -> lst nat -> nat -> lst nat -> o.

type   cex_ord_bad2   nat -> nat -> lst nat -> o.

type   cex_ord_bad_random   nat -> lst nat -> o.
type   cex_ord_bad_random2   nat -> nat -> lst nat -> o.

type nocex_rev_random   lst nat -> o.
type nocex_rev   lst nat -> o.

type   cex_rev   cert -> lst nat -> o.

type   main   o.
type   main1   o.

type   main2   o.
