module spy.

announce G :- coq.say ">>" G, fail.
spy G :- (coq.say ">Entering " G, G, coq.say ">Success  " G;
          coq.say ">Leaving  " G, fail).
