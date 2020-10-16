sig kernel.

% Helpers
type   memb     A -> list A -> o.

% Formulas and their terms
kind   prolog        type.
type   tt            prolog.
type   and, or       prolog -> prolog -> prolog.
type   some, nabla   (A -> prolog) -> prolog.
type   eq            A -> A -> prolog.

% Program and interpreter
type   prog      prolog -> prolog -> o.

kind   nprolog   type.
type   np        string -> prolog -> nprolog.
type   progs     prolog -> list nprolog -> o.

type   interp    prolog -> o.

% Certificates
kind   choice        type.
type   left, right   choice.

%kind   idx   type.

kind   cert            type.
type   tt_expert       cert -> o.
type   eq_expert       cert -> o.
type   or_expert       cert -> cert -> choice -> o.
type   and_expert      cert -> cert -> cert -> o.
type   some_expert     cert -> cert -> A -> o.
type   unfold_expert   list nprolog -> cert -> cert -> string -> o.

% Checker
type   check   cert -> prolog -> o.
