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

or_expert (qgen (qheight H)) (qgen (qheight H)) _Ch.
or_expert (qgen (qsize In Out)) (qgen (qsize In Out)) _Ch.

prod_expert (qgen (qheight H)) (qgen (qheight H)) (qgen (qheight H)).
prod_expert (qgen (qsize In Out)) (qgen (qsize In Mid)) (qgen (qsize Mid Out)).

prod_clerk (qgen (qheight H)) (qgen (qheight H)).
prod_clerk (qgen (qsize In Out)) (qgen (qsize In Out)).

unfold_expert Kn (qgen (qheight H)) (qgen (qheight H')) K :-
	std.mem Kn K,
	H > 0,
	H' is H - 1.
unfold_expert Kn (qgen (qsize In Out)) (qgen (qsize In' Out)) K :-
	std.mem Kn K,
	In > 0,
	In' is In - 1.

