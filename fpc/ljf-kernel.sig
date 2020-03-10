sig ljf-kernel.
accum_sig ljf-certificates.

type ljf_entry      cert -> form -> o.

%  The following should be hidden in the .mod file.

kind rhs                                 type.   % The RHS of the async sequent
type str, unk                     form -> rhs.   % The right-hand-side is either unknown or stored.

kind seq                                 type.   % sequents
type async           list form -> rhs  -> seq.   % async
type lfoc                 form -> form -> seq.   % left focus
type rfoc                         form -> seq.   % right focus
type storage               index -> form -> o.   % storage of formulas
type check                  cert -> seq  -> o.   % top-level predicate
