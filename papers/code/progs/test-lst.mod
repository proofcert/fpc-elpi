module test-lst.
accumulate kernel.
accumulate fpc-qbound.
accumulate prog.


%%%%%%%%%
% Tests %
%%%%%%%%%


% Simple generators, explicit existentials
check_ord_bad N L Cert :-
	check Cert
              (some N'\ some L'\ and (and (eq N N') (eq L L'))
                                     (and (is_nat N') (is_natlist L'))),
	interp (ord_bad L),
	interp (ins N L O),
	not (interp (ord_bad O)).


cex_ord_bad N L :-
	%check (qgen (qheight 4)) (and (is_nat N) (is_natlist L)),
	%interp (ord_bad L),
	check (qgen (qheight 4)) (ord_bad L),
	interp (ins N L O),
	not (interp (ord_bad O)).


% cex_ord_bad2 N1 N2 L :-
% 	check (qgen (qheight 4)) (and (is_nat N1) (and (is_nat N2) (is_natlist L))),
% 	interp (ord_bad (cons N2 L)),
% 	interp (leq N1 N2),
% 	not (interp (ord_bad (cons N1 (cons N2 L)))).





