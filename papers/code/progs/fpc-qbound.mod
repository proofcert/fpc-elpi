module fpc-qbound.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Simple term height and size bounds %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

tt_expert (qgen (qheight _)).
tt_expert (qgen (qsize In In)).

eq_expert (qgen (qheight _)).
eq_expert (qgen (qsize In In)).

and_expert (qgen (qheight H)) (qgen (qheight H)) (qgen (qheight H)).
and_expert (qgen (qsize In Out)) (qgen (qsize In Mid)) (qgen (qsize Mid Out)).

or_expert (qgen (qheight H)) (qgen (qheight H)) Ch.
or_expert (qgen (qsize In Out)) (qgen (qsize In Out)) Ch.

unfold_expert _ (qgen (qheight H)) (qgen (qheight H')) _ :-
	H > 0,
	H' is H - 1.
unfold_expert _ (qgen (qsize In Out)) (qgen (qsize In' Out)) _ :-
	In > 0,
	In' is In - 1.

some_expert (qgen Bound) (qgen Bound) T.

%%%%%%%%%%%%%%%%%
% Strict bounds %
%%%%%%%%%%%%%%%%%

%% Size bounds.

tt_expert (qgen (qidsize _)).
eq_expert (qgen (qidsize _)).
and_expert (qgen (qidsize Max)) Cert Cert' :-
	and_expert (qgen (qidsize' 0 Max)) Cert Cert'.
unfold_expert Gs (qgen (qidsize Max)) Cert Id :-
	unfold_expert Gs (qgen (qidsize' 0 Max)) Cert Id.

tt_expert (qgen (qidsize' _ _)).
eq_expert (qgen (qidsize' _ _)).
and_expert (qgen (qidsize' Size Max)) Cert Cert' :-
	Size < Max,
	Size' is Size + 1,
	and_expert (qgen (qrgsize Size' 0)) Cert Cert'.
unfold_expert Gs (qgen (qidsize' Size Max)) Cert Id :-
	Size < Max,
	Size' is Size + 1,
	unfold_expert Gs (qgen (qrgsize Size' 0)) Cert Id.
and_expert (qgen (qidsize' Size Max)) Cert Cert' :-
	Size < Max,
	Size' is Size + 1,
	and_expert (qgen (qidsize' Size' Max)) Cert Cert'.
unfold_expert Gs (qgen (qidsize' Size Max)) Cert Id :-
	Size < Max,
	Size' is Size + 1,
	unfold_expert Gs (qgen (qidsize' Size' Max)) Cert Id.

tt_expert (qgen (qrgsize Mid Mid)).
eq_expert (qgen (qrgsize Mid Mid)).
and_expert (qgen (qrgsize Max Min)) (qgen (qrgsize Max Mid)) (qgen (qrgsize Mid Min)).
unfold_expert _ (qgen (qrgsize Max Min)) (qgen (qrgsize Max' Min)) _ :-
	Max > 0,
	Max' is Max - 1.

%% Similarly for height. Exact bounds are inefficient in that there is no
%% immediate *and* simple way to cooordinate both sides of a conjunct so that at
%% least one reaches the required height. An easy workaround leads to some
%% duplication, which may be curbed by pairing with a size bound that drives
%% generation. The coordination of the increase in both kinds of bounds is also
%% a subject of further elaboration.

tt_expert (qgen (qidheight _)).
eq_expert (qgen (qidheight _)).
and_expert (qgen (qidheight Max)) Cert Cert' :-
	and_expert (qgen (qidheight' 0 Max)) Cert Cert'.
unfold_expert Gs (qgen (qidheight Max)) Cert Id :-
	unfold_expert Gs (qgen (qidheight' 0 Max)) Cert Id.

tt_expert (qgen (qidheight' _ _)).
eq_expert (qgen (qidheight' _ _)).
and_expert (qgen (qidheight' Size Max)) Cert Cert' :-
	Size < Max,
	Size' is Size + 1,
	and_expert (qgen (qrgheight Size' 0)) Cert Cert'.
unfold_expert Gs (qgen (qidheight' Size Max)) Cert Id :-
	Size < Max,
	Size' is Size + 1,
	unfold_expert Gs (qgen (qrgheight Size' 0)) Cert Id.
and_expert (qgen (qidheight' Size Max)) Cert Cert' :-
	Size < Max,
	Size' is Size + 1,
	and_expert (qgen (qidheight' Size' Max)) Cert Cert'.
unfold_expert Gs (qgen (qidheight' Size Max)) Cert Id :-
	Size < Max,
	Size' is Size + 1,
	unfold_expert Gs (qgen (qidheight' Size' Max)) Cert Id.

tt_expert (qgen (qrgheight Min Min)).
eq_expert (qgen (qrgheight Min Min)).
and_expert (qgen (qrgheight Max Min)) (qgen (qrgheight Max Min)) (qgen (qrgheight Max Min)).
and_expert (qgen (qrgheight Max Min)) (qgen (qrgheight Max Min)) (qgen (qheight Max')) :-
	Max > 0,
	Max' is Max - 1.
and_expert (qgen (qrgheight Max Min)) (qgen (qheight Max')) (qgen (qrgheight Max Min)) :-
	Max > 0,
	Max' is Max - 1.
unfold_expert _ (qgen (qrgheight Max Min)) (qgen (qrgheight Max' Min)) _ :-
	Max > 0,
	Max' is Max - 1.
