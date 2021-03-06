module fpc-qshrink.

%%%%%%%%%%%%%
% Shrinking %
%%%%%%%%%%%%%

tt_expert qcompute.

eq_expert qcompute.

and_expert qcompute qcompute qcompute.

or_expert qcompute qcompute Choice :-
	(
		Choice = left;
		Choice = right
	).

unfold_expert _Gs qcompute qcompute _Id.

some_expert (qshrink T Cert) Cert T.
some_expert (qshrink T Cert) Cert T' :-
	shrink T T'.

%%%%%%%%%%%%%%%%%%%%%%
% Witness extraction %
%%%%%%%%%%%%%%%%%%%%%%

tt_expert (qsubst qsubst0).
eq_expert (qsubst qsubst0).
and_expert (qsubst qsubst0) (qsubst qsubst0) (qsubst qsubst0).
or_expert (qsubst qsubst0) (qsubst qsubst0) _.
unfold_expert _ (qsubst qsubst0) (qsubst qsubst0) _.
some_expert (qsubst (qsubst1 T Cert)) (qsubst Cert) T.

% Get rid of shrinking and just use the certificate wrapped in qsubst?
subst2shrink qsubst0 qcompute.
subst2shrink (qsubst1 T Cert) (qshrink T Cert') :-
	subst2shrink Cert Cert'.
