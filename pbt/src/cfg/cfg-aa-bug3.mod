module cfg-aa-bug3.

prog (aa L)
%     (or % Bug 3
         (and (eq L (cons a W))
              (ss W)
         )
%         (and (eq L (cons b VW))
%              (and (append V W VW) (and (aa V) (aa W)))
%         )
%     )
     .
progs (aa S)
      [(np "aa1" (and (eq S (cons a W)) (ss W)))
%      ,(np "aa2" (and (eq S (cons b VW))  (and (append V W VW) (and (aa V) (aa W)))))
      ].
