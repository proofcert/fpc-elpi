module spy.

bracket Pre G Post :- coq.say Pre, term_to_string G S, coq.say S, coq.say Post.
announce G :- bracket ">>" G "\n", fail.
spy G :- (bracket ">Entering " G "\n", G, bracket ">Success  " G "\n";
          bracket ">Leaving  " G "\n", fail).
