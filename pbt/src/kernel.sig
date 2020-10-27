sig kernel.

% Helpers
type   memb     A -> list A -> o.

% Formulas and their terms
kind   term        type.
type   tt            term.
type   and, or       term -> term -> term.
type   some, nabla   (A -> term) -> term.
type   eq            A -> A -> term.

% Program and interpreter
% type   prog      term -> term -> o.

% kind   nterm   type.
% type   np        string -> term -> nterm.
% type   progs     term -> list nterm -> o.

type   interp    term -> o.
% added -AM
type   backchain    term -> term -> o.

% Certificates
kind   choice        type.
type   left, right   choice.

%kind   idx   type.

kind   cert            type.
type   tt_expert       cert -> o.
type   eq_expert       cert -> o.
type   or_expert       cert -> cert -> choice -> o.
type   and_expert      cert -> cert -> cert -> o.
type   prod_expert     cert -> cert -> cert -> o.
type   prod_clerk      cert -> cert -> o.
type   some_expert     cert -> cert -> A -> o.
type   unfold_expert   list constructor -> cert -> cert -> constructor -> o.

% Checker
kind   goal type.
type   go   term -> goal.
type   bc   term -> term -> goal.
type   check   cert -> goal -> o.
type get_head term -> term -> o.