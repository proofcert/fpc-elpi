module cfg-aa.

progs (aa S)
      [(np "aa1" (and (eq S (cons a W)) (ss W))),
      (np "aa2" (and (eq S (cons b VW))  (and (append V W VW) (and (aa V) (aa W)))))
      ].

% prog (aa (cons a W)) (ss W).
% prog (aa (cons b VW)) (and (append V W VW) (and (aa V) (aa W))).
