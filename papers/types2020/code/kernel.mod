module kernel.

/* check */
% Certificate checker
type   check    cert -> oo -> o.

check Cert tt          :- ttE Cert.
check Cert (eq T T)    :- eqE Cert.
check Cert (and G1 G2) :- andE Cert Cert1 Cert2,
                          check Cert1 G1, check Cert2 G2.
check Cert (or G1 G2) :- orE Cert Cert' LR, 
   ((LR = left,  check Cert' G1);
    (LR = right, check Cert' G2)).
check Cert (some G) :- someE Cert Cert1 T, check Cert1 (G T).
check Cert A :- unfoldE Cert Cert', prog A G, check Cert' G.
/* end */


prog (is_nat zero) (tt).
prog (is_nat (succ N)) (is_nat N).
prog (is_natlist null) (tt).
prog (is_natlist (cons Hd Tl)) (and (is_nat Hd) (is_natlist Tl)).