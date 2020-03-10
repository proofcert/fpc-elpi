sig deb-fpc.
accum_sig ljf-certificates.
accum_sig ljf-polarize, ljf-kernel.
accum_sig deb-fpc.

kind deb            type.
type apply          int -> list deb -> deb.
type lc             int ->      deb -> cert.
type args           int -> list deb -> cert.    
type idx                       int -> index.

type lambda          deb -> deb.

kind tm             type.
type app            tm -> tm -> tm.
type lam            (tm -> tm) -> tm.

type debi           int -> tm -> deb -> o.
type debe           int -> tm -> int -> (list deb -> list deb) -> o.
type var            int -> tm -> o.

type i,j,k          iform.  % atomic formulas = primitive types

type of                  tm -> iform -> o.
type example      int -> tm -> iform -> o.
type hope                        int -> o.
type test_all                           o.


