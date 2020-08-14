module stlc-wt-bug3.

progs (wt Ga E T)
      [(np "wt-var" (memb_elt (bind E T) Ga)),
       (np "wt-err" (eq E error)),
       (np "wt-tcc" (and (eq E (c M))
                         (tcc M T))),
       (np "wt-app" (and (eq E (app X Y))
                         (and (wt Ga X (funTy T H)) (wt Ga Y H)))), % exists H
       (np "wt-lam" (and (and (eq E (lam F Tx)) (eq T (funTy Tx T')))
                         (nabla x\ wt (cons (bind x Tx) Ga) (F x) T'))) ].

/*
prog (wt Ga M A) (memb (bind M A) Ga).
prog (wt _ error _) (tt).
prog (wt _ (c M) T) (tcc M T).
prog (wt Ga (app X Y) T) (and (wt Ga X (funTy T H)) (wt Ga Y H)). % exists H % Bug 3
prog (wt Ga (lam F Tx) (funTy Tx T)) (nabla x\ wt (cons (bind x Tx) Ga) (F x) T).
*/
