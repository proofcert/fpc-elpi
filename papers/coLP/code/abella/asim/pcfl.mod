module pcfl.

eval C C :- value C.
% lazy nu
% eval (s M) (s C) :- eval M C.
eval (case N M1 M2) C
	     :- eval N z, eval M1 C.
eval (case N M1 M2) C
	     :- eval N (s C'), eval (M2 C') C.

eval (lcase L M1 M2) C
	     :- eval L nl, eval M1 C.
eval (lcase L M1 M2) C
	     :- eval L (cns H T), eval (M2 H T) C.
eval (app F A) C :- eval F (abs  M), eval (M A) C.
eval (rec F) C :- eval (F (rec  F)) C.


value z.
value nl.
value (cns H T).
value (abs M).
 value (s N).
% lazy numbers!!!!


is_ty (arr S S') :- is_ty S, is_ty S'.
is_ty num.
is_ty (list S) :- is_ty S.

of z num.
of (s M) num :- of M num.
of (case N M1 M2) S
	    :- of N num, of M1 S, pi x\  of x num => of (M2 x) S.
% of nl (list S) :- is_ty S.
% if we want the invariant of M S -> is_ty S.
of nl (list S).
of (cns H T) (list S) :- of H S, of T (list S).
of (lcase L M1 M2) S':- 
   is_ty S,
   of L (list S), 
   of M1 S',
   pi h\ pi t\ of h S => 
      	       	  of t (list S) => of (M2 h t) S'.


of (app F A) S :- is_ty U, of F (arr U S), of A U.
of (abs  M) (arr S U) :- pi x\ (of x S => of (M x) U).
of (rec  F) S :- pi x\ (of x S => of (F x) S).
