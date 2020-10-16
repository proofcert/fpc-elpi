module prog.


%%%%%%%%%%%%%%
% Generators %
%%%%%%%%%%%%%%


progs (is_nat N)
      [(np "n_zero" (eq N zero)),
       (np "n_succ" (and (eq N (succ N'))
                         (is_nat N')))].

progs (is_natlist L)
      [(np "nl_null" (eq L null)),
       (np "nl_cons" (and (eq L (cons Hd Tl))
                     (and (is_nat Hd) (is_natlist Tl)))) ].


%%%%%%%%%%%%%%
% Predicates %
%%%%%%%%%%%%%%

progs (leq N M)
      [(np "le0" (eq N zero)),
       (np "les" (and (eq N (succ X)) (and (eq M (succ Y)) (leq X Y))))
      ].

progs (gt N M)
      [(np "le0" (and (eq M zero) (eq N (succ _K)))),
       (np "les" (and (eq N (succ X)) (and (eq M (succ Y)) (gt X Y))))
      ].

%
progs (ord_bad L)
      [(np "o_n" (eq L null)),
      (np "o_c1" (and (eq L (cons X null)) (is_nat X))),
      (np "oc_2" (and (eq L (cons X (cons Y Rs))) (and (leq X Y) (ord_bad Rs)))) %bug
            ].

progs (ord L)
      [(np "onl" (eq L null)),
      (np "oss" (and (eq L (cons X null)) (is_nat X))),
      (np "ocn" (and (eq L (cons X (cons Y Rs))) (and (leq X Y) (ord (cons Y Rs))))) 
            ].


progs (ins X L R)
      [(np "i_n" (and (eq L null) (and (eq R (cons X null)) (is_nat X)))),
      (np "i_s" (and (eq L (cons Y Ys)) (and (eq R  (cons X (cons Y Ys))) (leq X Y)))),
      (np "i_c" (and (eq L (cons Y Ys)) (and (eq R  (cons X Rs)) (and (gt X Y) (ins X Ys Rs)))))
            ].


% if we use the multiple "clause" approach, we'd use

% prog (leq zero _) tt.
% prog (leq (succ X) (succ Y)) (leq X Y).

% prog (gt (succ _) zero) tt.
% prog (gt (succ X) (succ Y)) (gt X Y).


% prog (ord null) tt.
% prog (ord (cons X null)) (is_nat X).
% prog (ord (cons X (cons Y Rs))) (and (leq X Y) (ord (cons Y Rs))).

% prog (ord_bad null) tt.
% prog (ord_bad (cons X null)) (is_nat X).
% prog (ord_bad (cons X (cons Y Rs))) (and (leq X Y) (ord_bad Rs)).

% prog (ins X null (cons X null)) (is_nat X).
% prog (ins X (cons Y Ys) (cons X (cons Y Ys))) (leq X Y).
% prog (ins X (cons Y Ys) (cons Y Rs)) (and (gt X Y) (ins X Ys Rs)).