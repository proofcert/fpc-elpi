sig kernel.
/* sigs */
kind   goal         type.
type   go           term -> term -> goal.
type   bc           term -> term -> list term -> goal.
type   check        cert -> goal -> o.
/* end */
/* interp */
type   interp    term -> o.
type   backchain    term -> term -> o.
/* end */
% Certificates
kind   choice        type.
type   left, right   choice.
kind   cert            type.
type   ttE       cert -> o.
type   eqE       cert -> o.
type   orE       cert -> cert -> choice -> o.
type   andE      cert -> cert -> cert -> o.
type   prodE     cert -> cert -> cert -> term -> o.
type   impE      cert -> cert -> o.
type   decideE   list constructor -> cert -> cert -> constructor -> o.

% Checker and interpreter
kind   goal         type.
type   go   term -> term -> goal.
type   bc   term -> term -> list term -> goal.
type   check   cert -> goal -> o.
type   flatten_app term -> term -> o.
