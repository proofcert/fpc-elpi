module cfg-bug3.
accumulate kernel.
accumulate cfg.
accumulate cfg-ss.
accumulate cfg-aa-bug3.
accumulate cfg-bb.

% Tests
sound Gen W N1 N2 :-
	check Gen (is_ablist W),
	interp (ss W),
	interp (count a W N1),
	interp (count b W N2),
	not (N1 = N2).

complete Gen W N :-
	check Gen (is_ablist W),
	interp (count a W N),
	interp (count b W N),
	not (interp (ss W)).

b1s W N1 N2 :-
	sound (qgen (qheight 2)) W N1 N2.

b1c W N :-
	complete (qgen (qheight 6)) W N.

b1sr W N1 N2 :-
	Ws = [(qw "ab-a" 1), (qw "ab-b" 1),
	      (qw "abl-null" 1), (qw "abl-cons" 3) ],
	sound (qtries 100 Ws) W N1 N2.

b1cr W N :-
	Ws = [(qw "ab-a" 1), (qw "ab-b" 1),
	      (qw "abl-null" 1), (qw "abl-cons" 3) ],
	complete (qtries 100 Ws) W N.
