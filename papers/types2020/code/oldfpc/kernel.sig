sig kernel.

/* sigs */
% Object-level formulas
kind oo        type.
type tt        oo.
type and, or   oo  -> oo -> oo.
type some      (A -> oo) -> oo.
type eq        A -> A  -> oo.

% Object-level Prolog clauses are
% stored as facts (prog A Body).
type prog      oo -> oo -> o.

% Certificates
kind cert          type.
kind choice        type.
type left, right   choice.

% The types for the expert predicates
type ttE, eqE               cert -> o.
type unfoldE        cert -> cert -> o.
type someE     cert -> cert -> A -> o.
type andE   cert -> cert -> cert -> o.
type orE  cert -> cert -> choice -> o.
/* end */

type   check    cert -> oo -> o.
% A sample program
kind   nat      type.
type   zero     nat.
type   succ     nat -> nat.
type   is_nat   nat -> oo.
type   leq      nat -> nat -> oo.
type   gt       nat -> nat -> oo.
type   is_natlist   lst nat -> oo.
kind   lst          type -> type.
type   null         lst A.
type   cons         A -> lst A -> lst A.
