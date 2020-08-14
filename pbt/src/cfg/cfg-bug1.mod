module cfg-bug1.
accumulate kernel.
accumulate cfg.
accumulate cfg-ss-bug1.
accumulate cfg-aa.
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

/*
qc :-
	random.self_init,
	b1sr W N1 N2,
	term_to_string W Wstr, print "W =", print Wstr,
	term_to_string N1 N1str, print "N1 =", print N1str,
	term_to_string N2 N2str, print "N2 =", print N2str.
*/