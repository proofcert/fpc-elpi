sig fpcs.
accum_sig kernel.

/* resources */
type  qheight  int -> cert.
type  qsize    int -> int -> cert.
type  <c>      cert ->  cert ->  cert.  infixr <c> 5.
/* end */

/* max */
kind max     type.
type max     max     -> cert.
type binary  max    -> max -> max.
type choose  choice -> max -> max.
type term    A      -> max -> max.
type empty   max.
/* end */

/* pairing */
type   <c>     cert ->  cert ->  cert.
infixr <c>     5.
/* end */

type l-or-r    list choice -> 
               list choice -> cert.

kind nat     type.
type zero    nat.
type succ    nat -> nat.

/* collect */
kind item                     type.
type c_nat             nat -> item.
type c_list_nat   list nat -> item.

type subterm      item -> item -> o.
type collect      list item -> 
                  list item -> cert.
/* end */
/* huniv */
type huniv   (item -> o) -> cert.
/* end */
