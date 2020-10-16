sig pcfl.

kind    tm, ty                   type.

type    z,nl            	 tm.
type    s 	       tm -> tm.
type    case                     tm -> tm -> (tm -> tm) -> tm.
type    lcase                     tm -> tm -> (tm -> tm -> tm) -> tm.
type    abs, rec                 (tm -> tm) -> tm.
type    app,cns                      tm -> tm -> tm.

type    num			                 ty.
type    list			                 ty -> ty.
type    arr                      ty -> ty -> ty.

type    is_ty                     ty -> o.
type    value			 tm -> o.
type    eval                     tm -> tm -> o.
type    of                       tm -> ty -> o.
