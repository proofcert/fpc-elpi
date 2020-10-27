module cfg-bb-bug2.

progs (bb S)
      [(np "bb1" (and (eq S (cons b W)) (ss W))),
      (np "bb2" (and (eq S (cons a VW))  (and (append V W VW) (and (bb V) (bb V)))))
      ].



prog (bb L)
     (or (and (eq L (cons b W))
              (ss W)
         )
         (and (eq L (cons a VW))
              (and (append V W VW) (and (bb V) (bb V))) % Bug 2
         )
     ).
