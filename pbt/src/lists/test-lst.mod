module test-lst.
accumulate nat.
accumulate lst.
accumulate kernel.
accumulate fpc-qbound.
accumulate fpc-qshrink.
accumulate fpc-pair.
accumulate fpc-rec.

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

debug_ord_bad N L Cert PPTrace :-
	check Cert
              (some N'\ some L'\ and (and (eq N N') (eq L L'))
                                     (and (is_nat N') (is_natlist L'))),
	check (rec Trace) (ord_bad L), pp Trace PPTrace,
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



% Currently two levels of backtracking: cex finding and shrinking over those.
cex_ord_bad_shrink Nbig Lbig Nsmall Lsmall :-
	check_ord_bad Nbig Lbig (pair (qgen (qheight 6)) (qsubst Qsubst)),
	subst2shrink Qsubst Qshrink,
	check_ord_bad Nsmall Lsmall Qshrink.

cex_ord_bad_debug N L PPTrace :-
	check_ord_bad N L (pair (qgen (qheight 6)) (rec Trace)),
	pp Trace PPTrace.

%%% reverse


%% hello world
nocex_rev  L :-
	check (qgen (qheight 6)) ( (is_natlist L)),
	interp (rev L R),
	not (interp (rev R L)).

%% our beloved example
cex_rev Gen L :-
	check Gen (is_natlist L),
	interp (rev L R),
	not (L = R).

cex_rev_debug Gen L Trace :-
	check Gen (some L'\ and (eq L L') (is_natlist L)),
	check (rec RawTrace) (rev L R),
	not (L = R),
	pp RawTrace Trace.

cex_rev_shrink Gen Lbig Lsmall Trace :-
	cex_rev_debug (pair Gen (qsubst Qsubst)) Lbig _,
	subst2shrink Qsubst Qshrink,
	cex_rev_debug Qshrink Lsmall Trace.

% RB: This clashes with the app in fpc-rec, and creates a loop.
%app [] L L.
%app (X:: Xs) Ys (X:: Zs) :-
%    app Xs Ys Zs.

mk_list 0 [] :- !.
mk_list N Ls :-
  N1 is N - 1,
  mk_list N1 Ns,
  app Ns [N] Ls.

cex_revIt Bound L :-
	mk_list Bound Range,
%	Range = [1,2,3,4,5,6,7,8,9,10],
	memb H Range,
	check (qgen (qheight H)) (is_natlist L),
	interp (rev L R),
	not (L = R).


