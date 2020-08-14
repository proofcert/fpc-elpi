module stlc-tcc-bug4.

progs (tcc E T) [
      (np "tcc-int" (and (eq E (toInt _)) (eq T intTy))),
      (np "tcc-nl" (and (eq E nl) (eq T listTy))),
      (np "tcc-hd" (and (eq E hd) (eq T (funTy listTy intTy)))),
      (np "tcc-tl" (and (eq E tl) (eq T (funTy listTy intTy)))),
      (np "tcc-cn" (and (eq E cns) (eq T (funTy intTy (funTy listTy intTy))))), % Bug 4
      (np "tcc-plus" (and (eq E plus) (eq T (funTy intTy (funTy intTy intTy))))) % Bug 4 addition
].


% prog (tcc (toInt _) intTy) (tt).
% prog (tcc nl listTy) (tt).
% prog (tcc hd (funTy listTy intTy)) (tt).
% prog (tcc tl (funTy listTy listTy)) (tt).
% prog (tcc cns (funTy intTy (funTy listTy intTy))) (tt). % Bug 4

