module stlc-bug1.
accumulate kernel.
accumulate stlc.
accumulate stlc-tcc.
accumulate stlc-wt-bug1.
accumulate stlc-value.
accumulate stlc-step.
accumulate stlc-tests.
accumulate nat.
accumulate lst.
accumulate fpc-qbound.
accumulate fpc-qrandom.
accumulate fpc-pair.

% Tests (prog)

% Note that pairing could be used to bound the size of random terms
% At the moment, some prog backtracking related to context variable selection
qcprog :-
	random.self_init,
	Ws = [(qw "n_zero" 1), (qw "n_succ" 1),
              (qw "ty-int" 1), (qw "ty-list" 1), (qw "ty-fun" 1),
              (qw "cnt-cns" 1), (qw "cnt-hd" 1), (qw "cnt-tl" 1), (qw "cnt-nl" 1), (qw "cnt-int" 1),
              (qw "exp-cnt" 1), (qw "exp-app" 1), (qw "exp-lam" 1), (qw "exp-err" 1) ],
	check (qtries 1500 Ws) (wt null E T),
	not (interp (progress E)),
	term_to_string E Estr, print "E =", print Estr,
	term_to_string T Tstr, print "T =", print Tstr.
