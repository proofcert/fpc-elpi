module random-test-lst.
accumulate nat.
accumulate lst.
accumulate kernel.
accumulate fpc-qbound.
accumulate fpc-qrandom.
accumulate fpc-qshrink.
accumulate fpc-pair.

%%%%%%%%%
% Tests %
%%%%%%%%%

% no of tries
tries 100.

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


cex_ord_bad2 N1 N2 L :-
	check (qgen (qheight 4)) (and (is_nat N1) (and (is_nat N2) (is_natlist L))),
	interp (ord_bad (cons N2 L)),
	interp (leq N1 N2),
	not (interp (ord_bad (cons N1 (cons N2 L)))).


cex_ord_bad_random N L :-
	Ws = [(qw "n_zero" 1), (qw "n_succ" 2),
              (qw "nl_null" 1), (qw "nl_cons" 2)],
	      tries NT,
	check (qtries NT Ws) (and (is_nat N) (is_natlist L)),
%	term_to_string N NStr, term_to_string L LStr,
%	print NStr, print " and list: ", print LStr,
	interp (ord_bad L),
	interp (ins N L O),
	not (interp (ord_bad O)).


cex_ord_bad_random2 N1 N2 L :-
	Ws = [(qw "n_zero" 1), (qw "n_succ" 2),
              (qw "nl_null" 1), (qw "nl_cons" 3)],
	      tries NT,
	check (qtries NT Ws) (and (is_nat N1) (and (is_nat N2) (is_natlist L))),
%	term_to_string N1 NStr1, term_to_string N2 NStr2, term_to_string L LStr,
%	print NStr1, print ", ", print NStr2, print ", ", print LStr,
	interp (ord_bad (cons N2 L)),
	interp (leq N1 N2),
	not (interp (ord_bad (cons N1 (cons N2 L)))).

% Currently two levels of backtracking: cex finding and shrinking over those.
cex_ord_bad_shrink Nbig Lbig Nsmall Lsmall :-
	check_ord_bad Nbig Lbig (pair (qgen (qheight 6)) (qsubst Qsubst)),
	subst2shrink Qsubst Qshrink,
	check_ord_bad Nsmall Lsmall Qshrink.

%%% reverse

% cexrev XS YS :-
% 	check (qgen (qheight 3)) (is_natlist XS),
% 	%check (qgen (qheight 3)) (is_eltlist YS),
% 	interp (rev XS YS),
% 	not (XS = YS).


% the property is true
nocex_rev_random  L :-
	Ws = [(qw "nl_null" 1), (qw "nl_cons" 3)],
	      tries NT,
	check (qtries NT Ws) ((is_natlist L)),
%	term_to_string L LStr,
%	print "list: ", print LStr,
	interp (rev L R),
	not (interp (rev R L)).

%% hello world
nocex_rev  L :-
	check (qgen (qheight 6)) ( (is_natlist L)),
	interp (rev L R),
	not (interp (rev R L)).

%% our beloved example
cex_rev Gen L :-
	check Gen (some L'\ and (eq L L') (is_natlist L')),
	interp (rev L R),
	not (L = R).

cex_gen_shrink Lbig Lsmall :-
	cex_rev (pair (qtries 100 []) (qsubst Qsubst)) Lbig,
	subst2shrink Qsubst Qshrink,
	cex_rev Qshrink Lsmall.


main  :-
 	cex_ord_bad_random _N _L.
 main2  :-
 	cex_ord_bad_random2  _N1 _N2 _L.

 main1 :-
       nocex_rev_random _L.
