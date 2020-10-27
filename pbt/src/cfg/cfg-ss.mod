module cfg-ss.

prog (ss null) tt.
prog (ss (cons b W)) (aa W).
prog (ss (cons a W)) (bb W).

progs (ss S) [
      (np "s1" (eq S null)),
      (np "s2" (and (eq S (cons b W)) (aa W))),
      (np "s3" (and (eq S (cons a W)) (bb W)))
      ].