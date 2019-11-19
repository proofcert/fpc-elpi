sig coq-fpc.
accum_sig ljf-polarize, ljf-kernel.
accum_sig stlc-fpc.

kind tm             type.
type app            tm -> tm -> tm.
type lam            (tm -> tm) -> tm.

type debi           int -> tm -> deb -> prop.
type debe           int -> tm -> int -> (list deb -> list deb) -> prop.
type vr             int -> tm -> prop.

type i,j,k          iform.  % atomic formulas = primitive types

type of                  tm -> iform -> prop.
type example      int -> tm -> iform -> prop.
type hope                        int -> prop.
type test_all                           prop.
