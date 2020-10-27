module cfg-ss-bug1.

prog (ss null) tt.
prog (ss (cons b W)) (ss W). % Bug 1
prog (ss (cons a W)) (bb W).


progs (ss W)
      [(np "se" (eq W null)),
       (np "sb" (and (eq W (cons b W'))( ss W'))), % Bug 1
       (np "sa" (and (eq W (cons a W'))( bb W')))].

