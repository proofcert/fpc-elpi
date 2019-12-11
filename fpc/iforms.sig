sig iforms.
accum_sig ljf-formulas.

% The syntactic categories for intuitionistic formulas and for first-order individuals.

/* iformsig */
kind iform, i       type.  
type imp            iform -> iform -> iform.
type forall         (i -> iform) -> iform.
/* end */

type tt, ff         iform.
type and, or        iform -> iform -> iform.
type exists         (i -> iform) -> iform.

infixr and  6.
infixr or   5.
infixr imp  4.

type atomic, non_atomic                   iform -> prop.

type polarize_neg, polarize_pos   iform -> prop.
% These later two predicates are expected to divide all atomic 
% formulas into non-overlapping sets of positive and negative atoms.
