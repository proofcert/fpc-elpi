module cfg-bb.

progs (bb S)
      [(np "bb1" (and (eq S (cons b W)) (ss W))),
      (np "bb2" (and (eq S (cons a VW))  (and (append V W VW) (and (bb V) (bb W)))))
      ].



% prog (bb (cons b W)) (ss W).
% prog (bb (cons a VW)) (and (append V W VW) (and (bb V) (bb W))).
