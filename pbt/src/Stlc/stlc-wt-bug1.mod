module stlc-wt-bug1.

% Bug 1
progs (wt Ga E T)
      [(np "wt-var" (memb_elt (bind E T) Ga)),
       (np "wt-err" (eq E error)),
       (np "wt-tcc" (and (eq E (c M))
                         (tcc M T))),
       (np "wt-app" (and (eq E (app X Y))
                         (and (wt Ga X (funTy H T)) (wt Ga Y T)))), % exists H
       (np "wt-lam" (and (and (eq E (lam F Tx)) (eq T (funTy Tx T')))
                         (nabla x\ wt (cons (bind x Tx) Ga) (F x) T'))) ].

/*
prog (wt Ga M A) (memb_elt (bind M A) Ga).
prog (wt _ error _) (tt).
prog (wt _ (c M) T) (tcc M T).
prog (wt E (app M N) U) (and (wt E M (funTy T U)) (wt E N U)). % exists T
prog (wt Ga (lam F Tx) (funTy Tx T)) (nabla x\ wt (cons (bind x Tx) Ga) (F x) T).
*/
