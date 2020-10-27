module stlc-bug9.
accumulate kernel.
accumulate stlc.
accumulate stlc-tcc.
accumulate stlc-wt-bug9.
accumulate stlc-value.
accumulate stlc-step.
accumulate nat.
accumulate lst.
accumulate fpc-qbound.
accumulate fpc-pair.

% Tests
% wt generator does not work with Elpi here (non-pattern unification)
cexpres E E' T :-
	itsearch H SH,
	check (pair (qgen (qheight H)) (qgen (qsize SH _))) (is_exp' null E),
	%check (qgen (qheight 3)) (is_exp E'),
	%check (qgen (qheight 1)) (is_ty T),
	interp (step E E'),
	interp (wt null E T),
	not (interp (wt null E' T)).
