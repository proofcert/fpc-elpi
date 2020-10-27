module stlc-subexp.
accumulate kernel.
accumulate stlc.
accumulate stlc-wt.
accumulate stlc-value.
accumulate stlc-step.

prog (is_pexp Ctx (app Exp1 Exp2)) (and (is_pexp Ctx Exp1) (is_pexp Ctx Exp2)).
prog (is_pexp Ctx (lam ExpX Ty)) (and (nabla x\ is_pexp (cons x Ctx) (ExpX x)) (is_ty Ty)).
prog (is_pexp Ctx X) (tt) :-
	memb_ctx Ctx X.

% Tests

cexsexp E E' T :-
	check (qgen (qsize 8 _)) (step E E'), % (is_exp' null E),
%	interp (step E E'),
	interp (wt null E' T),
	not (interp (wt null E T)).

unty E   :-
	check (qgen (qsize 8 _)) (is_pexp null E),
	not (interp (wt null E T)).
% uninteresting --- needs to be mstep
divrg E   :-
	check (qgen (qsize 8 _)) (is_exp' null E),
	not (interp (step E V)).

% cexsexp E E' T :-
% 	check (pair (qgen (qheight 4)) (qgen (qsize 8 _))) (is_exp' null E),
% 	%check (qgen (qheight 4)) (is_exp E'),
% 	%check (qgen (qheight 1)) (is_ty T),
% 	interp (step E E'),
% 	interp (wt null E' T),
% 	not (interp (wt null E T)).