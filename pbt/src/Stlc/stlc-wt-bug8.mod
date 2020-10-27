module stlc-wt-bug8.

progs (wt Ga E T)
      [(np "wt-var" (and (eq T intTy) % Bug 8
                         (memb_elt (bind E A) Ga))),
       (np "wt-err" (eq E error)),
       (np "wt-tcc" (and (eq E (c M))
                         (tcc M T))),
       (np "wt-app" (and (eq E (app X Y))
                         (and (wt Ga X (funTy H T)) (wt Ga Y H)))), % exists H
       (np "wt-lam" (and (and (eq E (lam F Tx)) (eq T (funTy Tx T')))
                         (nabla x\ wt (cons (bind x Tx) Ga) (F x) T'))) ].

/*
prog (wt Ga M intTy) (memb (bind M A) Ga). % Bug 8, exists A
prog (wt _ error _) (tt).
prog (wt _ (c M) T) (tcc M T).
prog (wt Ga (app X Y) T) (and (wt Ga X (funTy H T)) (wt Ga Y H)). % exists H
prog (wt Ga (lam F Tx) (funTy Tx T)) (nabla x\ wt (cons (bind x Tx) Ga) (F x) T).
*/
