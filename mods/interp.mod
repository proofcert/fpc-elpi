module interp.
%%%%%%%%%%%%%%%%	  
type announce, spy    o -> o.
type bracket          string -> o -> string -> o.  % Auxiliary

bracket Pre G Post :- print Pre, term_to_string G S, print S, print Post.
announce G :- bracket ">>" G "\n", fail.
spy G :- (bracket ">Entering " G "\n", G, bracket ">Success  " G "\n";
          bracket ">Leaving  " G "\n", fail).
%%%%%%%%%%%%%%%%	  

prv A B C     :- announce (prv A B C).
bc  A B C D E :- announce (bc  A B C D E).

%%%%%%%%%%%%%%%%

copy (app M N) (app M' N') :- copy M M', copy N N'.
copy (abs R)   (abs R')    :- pi x\ copy x x => copy (R x) (R' x).
subst R T S :- pi x\ copy x T => copy (R x) S.

%% Focused proof search using prv (for async) and bc (for sync).

prv Cert (imp B C) (abs R) :- pi x\ copy x x => hyp B x => prv Cert C (R x).
prv Cert i T               :- decide_expert Cert Cert', hyp D F, bc Cert' D i F T.

bc Cert i i T T :- init_expert Cert.
bc Cert (imp B C) i F T :- spy(bc_expert Cert Cert' Cert''),
        (pi x\ copy x x => bc Cert' C i x (R x)), 
        spy(subst R (app F S) T),
        prv Cert'' B S.

init_expert   (depth C).
decide_expert (depth C) (depth C') :- C > 0, C' is (C - 1).
bc_expert     (depth C) (depth C) (depth C).

init_expert   (size I I).
decide_expert (size I O) (size I' O) :- I > 0, I' is (I - 1).
bc_expert     (size I O) (size I M) (size M O).

example 1 (imp i i).
example 2 (imp i (imp i i)).
example 3 (imp i (imp (imp i i) i)).
example 4 (imp i (imp (imp i (imp i i)) i)).

% Loops after finding the first solution
% prv (depth 2) Ty (abs (W1\ W1)).
