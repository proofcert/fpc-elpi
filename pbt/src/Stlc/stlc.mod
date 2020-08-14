module stlc.

%% Lambda-terms

progs (is_ty T)
      [(np "ty-int"  (eq T intTy)),
       (np "ty-list" (eq T listTy)),
       (np "ty-fun"  (and (eq T (funTy Ty1 Ty2))
                          (and (is_ty Ty1) (is_ty Ty2)))) ].

shrink (funTy Ty1 _) Ty1.
shrink (funTy Ty1 _) Ty1' :- shrink Ty1 Ty1'.
shrink (funTy _ Ty2) Ty2.
shrink (funTy _ Ty2) Ty2' :- shrink Ty2 Ty2'.
shrink (funTy Ty1 Ty2) (funTy Ty1' Ty2) :- shrink Ty1 Ty1'.
shrink (funTy Ty1 Ty2) (funTy Ty1 Ty2') :- shrink Ty2 Ty2'.
shrink (funTy Ty1 Ty2) (funTy Ty1' Ty2') :- shrink Ty1 Ty1', shrink Ty2 Ty2'.

progs (is_cnt C)
      [(np "cnt-cns" (eq C cns)),
       (np "cnt-hd"  (eq C hd)),
       (np "cnt-tl"  (eq C tl)),
       (np "cnt-nl"  (eq C nl)),
       (np "cnt-int" (and (eq C (toInt I))
                          (is_nat I))) ].

% Integrate tcc in the generator
progs (is_tcnt C Ty)
      [(np "cnt-cns" (and (eq C cns) (eq Ty (funTy intTy (funTy listTy listTy))))),
       (np "cnt-hd"  (and (eq C hd)  (eq Ty (funTy listTy intTy)))),
       (np "cnt-tl"  (and (eq C tl)  (eq Ty (funTy listTy listTy)))),
       (np "cnt-nl"  (and (eq C nl)  (eq Ty listTy))),
       (np "cnt-int" (and (and (eq C (toInt I)) (eq Ty intTy))
                          (is_nat I))) ].

% shrink (to_int I) (to_int I') :- shrink I I'.


progs (is_exp E)
      [(np "exp-cnt" (and (eq E (c Cnt))
                          (is_cnt Cnt))),
       (np "exp-app" (and (eq E (app Exp1 Exp2))
                          (and (is_exp Exp1) (is_exp Exp2)))),
       (np "exp-lam" (and (eq E (lam ExpX Ty))
                          (and (nabla x\ is_exp (ExpX x)) (is_ty Ty)))),
       (np "exp-err" (eq E error)) ].

% Integrate wt in the generator
progs (is_texp E Ty)
      [(np "exp-cnt" (and (eq E (c Cnt))
                          (is_tcnt Cnt Ty))),
       (np "exp-app" (and (eq E (app Exp1 Exp2))
                          (and (is_texp Exp1 (funTy H Ty)) (is_texp Exp2 H)))),
       (np "exp-lam" (and (and (eq E (lam ExpX Tx)) (eq Ty (funTy Tx T)))
                          (and (nabla x\ is_texp (ExpX x) T) (is_ty Tx)))),
       (np "exp-err" (and (eq E error)
                          (is_ty Ty))) ].

shrink (c Cnt) (c Cnt') :- shrink Cnt Cnt.

shrink (app Exp1 _) Exp1.
shrink (app Exp1 _) Exp1' :- shrink Exp1 Exp1'.
shrink (app _ Exp2) Exp2.
shrink (app _ Exp2) Exp2' :- shrink Exp2 Exp2'.
shrink (app Exp1 Exp2) (app Exp1' Exp2) :- shrink Exp1 Exp1'.
shrink (app Exp1 Exp2) (app Exp1 Exp2') :- shrink Exp2 Exp2'.
shrink (app Exp1 Exp2) (app Exp1' Exp2') :- shrink Exp1 Exp1', shrink Exp2 Exp2'.

shrink (lam ExpX Ty) Exp :- pi x\ ExpX x = Exp.
shrink (lam ExpX Ty) Exp :- pi x\ shrink (ExpX x) Exp.
shrink (lam ExpX Ty) (lam ExpX' Ty) :- pi x\ shrink (ExpX x) (ExpX' x).
shrink (lam ExpX Ty) (lam ExpX Ty') :- shrink Ty Ty'.
shrink (lam ExpX Ty) (lam ExpX' Ty') :- (pi x\ shrink (ExpX x) (ExpX' x)), shrink Ty Ty'.

% Maintaining a context of lambda variables

progs (is_exp' Ctx E)
      [(np "c-exp-cnt" (and (eq E (c Cnt))
                          (is_cnt Cnt))),
       (np "c-exp-app" (and (eq E (app Exp1 Exp2))
                          (and (is_exp' Ctx Exp1) (is_exp' Ctx Exp2)))),
       (np "c-exp-lam" (and (and (eq E (lam ExpX Ty)) (eq Ctx  Ctx'))
                          (and (nabla x\ is_exp' (cons x Ctx') (ExpX x)) (is_ty Ty)))),
       (np "c-exp-err" (eq E error)) ].


prog (is_exp' _ (c Cnt)) (is_cnt Cnt).
prog (is_exp' Ctx (app Exp1 Exp2)) (and (is_exp' Ctx Exp1) (is_exp' Ctx Exp2)).
prog (is_exp' Ctx (lam ExpX Ty)) (and (nabla x\ is_exp' (cons x Ctx) (ExpX x)) (is_ty Ty)).
prog (is_exp' _ error) (tt).
prog (is_exp' Ctx X) (tt) :-
	memb_ctx Ctx X.

% For this selection to count as one unfolding, we run it outside of prog
memb_ctx (cons X Ctx) X.
memb_ctx (cons _ Ctx) X :-
	memb_ctx Ctx X.

prog (is_elt (bind E T)) (and (is_exp E) (is_ty T)).

prog (is_eltlist null) (tt).
prog (is_eltlist (cons E L)) (and (is_elt E) (is_eltlist L)).

% "Polymorphic" membership
prog (memb_elt X (cons X _)) (tt).
prog (memb_elt X (cons Y Gamma)) (memb_elt X Gamma).

prog (is_error error) (tt).
prog (is_error (app (c hd) (c nl))) (tt).
prog (is_error (app (c tl) (c nl))) (tt).
prog (is_error (app E1 _)) (is_error E1).
prog (is_error (app E1 E2)) (and (is_value E1) (is_error E2)).

prog (progress V) (is_value V).
prog (progress E) (is_error E).
prog (progress M) (step M N).

range [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18].

itsearch H SH :-
   range Range,
   memb H Range,
   SH is H * 3. % can be changed
