% Version of official code copied here and edited for possible inclusion in the paper
sig deb-fpc.
accum_sig ljf-certificates.
accum_sig deb-fpc.

/* start */
kind deb                              type.
type lambda                     deb -> deb.
type apply          int -> list deb -> deb.
type idx                      int -> index.
type lc                 int -> deb -> cert.
type args          int -> list deb -> cert.    
/* end */

kind tm             type.
type ap             tm -> tm -> tm.
type la             (tm -> tm) -> tm.

type debi           int -> tm -> deb -> prop.
type debe           int -> tm -> int -> (list deb -> list deb) -> prop.
type vr             int -> tm -> prop.

% type i,j,k          iform.  % atomic formulas = primitive types

% type of                  tm -> iform -> prop.
% type example      int -> tm -> iform -> prop.
% type hope                        int -> prop.
% type test_all                           prop.


