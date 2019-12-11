sig maximal-fpc.
accum_sig lkf-certificates.
kind nat    type.
type zero   nat.
type succ   nat -> nat. % Successor
/* start */
kind max type.
type ix                 nat -> index.
type max          nat -> max -> cert.
type max0                        max.
type max1                 max -> max.
type max2          max -> max -> max.
type maxa               index -> max.
type maxi        index -> max -> max.
type maxv          (i -> max) -> max.
type maxt            i -> max -> max.
type maxf  form -> max -> max -> max.
type maxc       choice -> max -> max.
/* end */
