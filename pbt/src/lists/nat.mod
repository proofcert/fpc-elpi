module nat.

%%%%%%%%%%%%%
% Shrinkers %
%%%%%%%%%%%%%

shrink (succ N) N.
shrink (succ N) N' :- shrink N N'.

%%%%%%%%%%%%%%
% Generators %
%%%%%%%%%%%%%%

%TODO: Check Elpi bug on )]
progs (is_nat N)
      [(np "n_zero" (eq N zero)),
       (np "n_succ" (and (eq N (succ N'))
                         (is_nat N')))].

%%%%%%%%%%%%%%
% Predicates %
%%%%%%%%%%%%%%

progs (leq N M)
      [(np "le0" (eq N zero)),
       (np "les" (and (eq N (succ X)) (and (eq M (succ Y)) (leq X Y))))
      ].

%TODO: Fix clause names.
progs (gt N M)
      [(np "le0" (and (eq M zero) (eq N (succ _K)))),
       (np "les" (and (eq N (succ X)) (and (eq M (succ Y)) (gt X Y))))
      ].
