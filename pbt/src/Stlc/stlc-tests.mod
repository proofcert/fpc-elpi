module stlc-tests.

% Certificate generation

itsearch_h (qgen (qheight H)) :-
	itsearch H _.

itsearch_s (qgen (qsize SH _)) :-
	itsearch _ SH.

itsearch_hs (pair (qgen (qheight H)) (qgen (qsize SH _))) :-
	itsearch H SH.

% Test templates

cexprog Gen E T :-
	check Gen (wt null E T),
	not (interp (progress E)).

cexpres Gen E E' T :-
	check Gen (wt null E T),
	interp (step E E'),
	not (interp (wt null E' T)).

% Concrete iterated tests

cexprog_h E T :-
	itsearch_h Cert,
	cexprog Cert E T.

cexprog_s E T :-
	itsearch_s Cert,
	cexprog Cert E T.

cexprog_hs E T :-
	itsearch_hs Cert,
	cexprog Cert E T.

cexpres_h E E' T :-
	itsearch_h Cert,
	cexpres Cert E E' T.

cexpres_s E E' T :-
	itsearch_s Cert,
	cexpres Cert E E' T.

cexpres_hs E E' T :-
	itsearch_hs Cert,
	cexpres Cert E E' T.
