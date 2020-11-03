sig kernel.
/* sigs */
kind   goal         type.
type   go   term -> term -> goal.
type   bc   term -> term -> list term -> goal.
type   check   cert -> goal -> o.
/* end */
/* interp */
type   interp    term -> o.
type   backchain    term -> term -> o.
/* end */
% Certificates
kind   choice        type.
type   left, right   choice.
kind   cert            type.
type   tt_expert       cert -> o.
type   eq_expert       cert -> o.
type   or_expert       cert -> cert -> choice -> o.
type   and_expert      cert -> cert -> cert -> o.
type   prod_expert     cert -> cert -> cert -> o.
type   imp_expert      cert -> cert -> o.
type   unfold_expert   list constructor -> cert -> cert -> constructor -> o.

% Checker and interpreter
kind   goal         type.
type   go   term -> term -> goal.
type   bc   term -> term -> list term -> goal.
type   check   cert -> goal -> o.
type   flatten_app term -> term -> o.
