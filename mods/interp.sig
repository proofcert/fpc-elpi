sig interp.

kind fm  type.
type i   fm.
type imp fm -> fm -> fm.

kind tm  type.
type app tm -> tm -> tm.
type abs (tm -> tm) -> tm.

kind cert type.
type depth             int -> cert.
type size              int -> int -> cert.

type copy              tm -> tm -> o.
type subst             (tm -> tm) -> tm -> tm -> o.

type hyp               fm -> tm -> o.
type prv               cert -> fm -> tm -> o.
type bc                cert -> fm -> fm -> tm -> tm -> o.

type init_expert       cert -> o.
type decide_expert     cert -> cert -> o.
type bc_expert         cert -> cert -> cert -> o.

type example          int -> fm -> o.
