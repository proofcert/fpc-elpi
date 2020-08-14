sig stlc.
accum_sig kernel.
accum_sig nat.
accum_sig lst.

kind   cnt, exp, ty, elt   type.

type   c        cnt -> exp.
type   app      exp -> exp -> exp.
type   lam      (exp -> exp) -> ty -> exp.
type   error    exp.

type   cns, hd, tl, nl   cnt.
type   toInt             nat -> cnt.

type   intTy    ty.
type   funTy    ty -> ty -> ty.
type   listTy   ty.
type   is_nat   nat -> prolog.
type   bind         exp -> ty -> elt.
type   is_ty        ty -> prolog.
type   is_cnt       cnt -> prolog.
type   is_tcnt      cnt -> ty ->  prolog.     %   (As above, with types)
type   is_exp       exp -> prolog.            % Simple exp generation
type   is_texp      exp -> ty -> prolog.      %   (As above, with types)
type   is_exp'      lst exp -> exp -> prolog. % Maintaining list of lambda vars
type   memb_ctx     lst exp -> exp -> o.
type   is_elt       elt -> prolog.
type   is_eltlist   lst elt -> prolog.
type   tcc          cnt -> ty -> prolog.
type   memb_elt     elt -> lst elt -> prolog.
type   wt           lst elt -> exp -> ty -> prolog.
type   is_value     exp -> prolog.
type   is_error     exp -> prolog.
type   step         exp -> exp -> prolog.
type   progress     exp -> prolog.

type   range      list int -> o.
type   itsearch   int -> int -> o.
