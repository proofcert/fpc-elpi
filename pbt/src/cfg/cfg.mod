module cfg.

progs (is_ab AB)
      [(np "ab-a" (eq AB a)),
       (np "ab-b" (eq AB b)) ].

progs (is_ablist L)
      [(np "abl-null" (eq L null)),
       (np "abl-cons" (and (eq L (cons Hd Tl))
                           (and (is_ab Hd) (is_ablist Tl)))) ].

% trusted, not explained
prog (neq a b) tt.
prog (neq b a) tt.

prog (count _ null zero) tt.
prog (count X (cons X Xs) (succ N)) (count X Xs N).
prog (count X (cons Y Xs) N) (and (neq X Y) (count X Xs N)).
prog (append null L L) tt.
prog (append (cons X L) K (cons X M)) (append L K M).

shrink (cons Hd Tl) Tl.
shrink (cons Hd Tl) (cons Hd Tl') :- shrink Tl Tl'.
