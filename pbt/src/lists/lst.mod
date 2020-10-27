module lst.
%accumulate kernel.

%%%%%%%%%%%%%
% Shrinkers %
%%%%%%%%%%%%%

shrink (cons Hd Tl) Tl.
shrink (cons Hd Tl) Tl' :- shrink Tl Tl'.
shrink (cons Hd Tl) (cons Hd' Tl) :- shrink Hd Hd'.
shrink (cons Hd Tl) (cons Hd Tl') :- shrink Tl Tl'.
shrink (cons Hd Tl) (cons Hd' Tl') :- shrink Hd Hd', shrink Tl Tl'.

%%%%%%%%%%%%%%
% Generators %
%%%%%%%%%%%%%%

progs (is_natlist L)
      [(np "nl_null" (eq L null)),
       (np "nl_cons" (and (eq L (cons Hd Tl))
                     (and (is_nat Hd) (is_natlist Tl)))) ].

%%%%%%%%%%%%%%
% Predicates %
%%%%%%%%%%%%%%

progs (ord_bad L)
      [(np "o_n" (eq L null)),
      (np "o_c1" (and (eq L (cons X null)) (is_nat X))),
      (np "oc_2" (and (eq L (cons X (cons Y Rs))) (and (leq X Y) (ord_bad Rs))))
            ].

progs (ins X L R)
      [(np "i_n" (and (eq L null) (and (eq R (cons X null)) (is_nat X)))),
      (np "i_s" (and (eq L (cons Y Ys)) (and (eq R  (cons X (cons Y Ys))) (leq X Y)))),
      (np "i_c" (and (eq L (cons Y Ys)) (and (eq R  (cons X Rs)) (and (gt X Y) (ins X Ys Rs)))))
            ].

progs (rev L R)
   [(np "rn" (and (eq L null) (eq R null))),
    (np "rc" (and (eq L (cons X Xs)) (and (rev Xs Ts) (append Ts (cons X null) R))))
   ].

progs (append Xs Ys Zs)
      [(np "an" (and (eq Xs null) (eq Ys Zs))),
       (np "ac" (and (eq Xs (cons X' Xs')) (and (append Xs' Ys Zs') (eq Zs (cons X Zs')))))
      ].
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

% prog (append null L L) tt.
% prog (append (cons X L) K (cons X M)) (append L K M).

