module fpc-qrandom.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Randomized "quick"-style FPC %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Helper predicates

member X (X :: L) :- !.
member X (Y :: L) :- member X L.

% For each possible named clause that can be selected, find its weight in the
% table of generators (currently assuming the tables are exhaustive). Return the
% sum of weights as well as the subset of rows in the table of generators
% corresponding to the set of selectable clauses. In the second return argument,
% the order of the rows matches their appearance in the full table of generators
% (and in a first approximation, this is not done tail recursively).
sum_weights [] _ 0 [].
sum_weights ((np ClauseId _) :: Clauses) Weights Sum CleanWeights :-
	% Assume a matching tuple is always present
	member (qw ClauseId Weight) Weights,
	sum_weights Clauses Weights SubTotal SubWeights,
	Sum is SubTotal + Weight,
	CleanWeights = (qw ClauseId Weight) :: SubWeights.
sum_weights ((np ClauseId _) :: Clauses) Weights Sum CleanWeights :-
	% Fallback for clauses where no matching tuple is present
	% It generates a uniform distribution where no distribution is given
	not (member (qw ClauseId Weight) Weights),
	sum_weights Clauses Weights SubTotal SubWeights,
	Sum is SubTotal + 1,
	CleanWeights = (qw ClauseId 1) :: SubWeights.

% Take a lost of weighed clauses summing up to N = N1, N2, ... Nk; and a number
% in the range [0, N). Select the clause according to the distribution:
%   0 .. N1 - 1
%   N1 .. (N2 - N1 - 1)
%   ...
select_clause Countdown ((qw ClauseId Weight) :: _) ClauseId :-
	Countdown < Weight.
select_clause Countdown ((qw _ Weight) :: Weights) ClauseId :-
	Countdown >= Weight,
	Countdown' is Countdown - Weight,
	select_clause Countdown' Weights ClauseId.

%% Random generation of data

tt_expert (qrandom _).

eq_expert (qrandom _).

and_expert (qrandom Ws) (qrandom Ws) (qrandom Ws).

or_expert (qrandom Ws) (qrandom Ws) Choice :-
	(
		Choice = left;
		Choice = right
	).

% only for elpi
unfold_expert Gs (qrandom Ws) (qrandom Ws) Id :-
	sum_weights Gs Ws Sum SubWs,
%	term_to_string Sum SumStr,
%	Msg is "Select a number [0-" ^ SumStr ^ "):",
%	print Msg,
%%	read Random,
	random.int Sum Random,
%	term_to_string Random RandomStr,
%	print Random,
	select_clause Random SubWs Id,
	print Id.

%% Iteration on number of tries (somewhat redundant encoding)

and_expert (qtries N W) (qrandom W) (qrandom W) :-
	N > 0.
and_expert (qtries N W) Cert Cert' :-
	N > 0,
	N' is N - 1,
% print "Retrying",
	and_expert (qtries N' W) Cert Cert'.

unfold_expert Gs (qtries N W) Cert Id :-
	N > 0,
	unfold_expert Gs (qrandom W) Cert Id.
unfold_expert Gs (qtries N W) Cert Id :-
	N > 0,
	N' is N - 1,
% print "Retrying",
	unfold_expert Gs (qtries N' W) Cert Id.

some_expert (qtries N W) (qtries N W) T.
some_expert (qrandom W) (qrandom W) T.
