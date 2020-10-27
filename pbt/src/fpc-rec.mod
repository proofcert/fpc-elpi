module fpc-rec.

tt_expert (rec tend).
eq_expert (rec tend).
and_expert (rec (tand T1 T2)) (rec T1) (rec T2).
or_expert (rec T) (rec T) Choice :- (Choice = left; Choice = right).
unfold_expert _ (rec (tseq Id T)) (rec T) Id.
some_expert (rec T) (rec T) _.

app nil L L.
app (X :: L1) L2 (X :: L3) :- app L1 L2 L3.

pp tend [].
pp (tseq S T) (S :: L) :- pp T L.
pp (tand T1 T2) L :- pp T1 L1, pp T2 L2, app L1 L2 L.
