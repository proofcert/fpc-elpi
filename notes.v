(*
the atomic case of the interpreter:
interp (app [global (indt Prog) | Args] as Atom)

means Prog is predicate and Args are its args

e.g. (le 1 2)    is 

Prog = <<le>>
Args = list of encodings of 1 and 2
e.g. 1 is app [global (indc «S»), global (indc «O»)]

Then we collect the list of constructors (the available clauses)
and try to backchain on the atom

Unclear:

interp {{nat}}. 
interp (sort _) .
*)


(* WHY [auto] SUCKS:

 from UseAuto.v in SF:

 Note that proof search tactics never perform any rewriting
    step (tactics [rewrite], [subst]), nor any case analysis on an
    arbitrary data structure or property (tactics [destruct] and
    [inversion]), nor any proof by induction (tactic [induction]). So,
    proof search is really intended to automate the final steps from
    the various branches of a proof. It is not able to discover the
    overall structure of a proof. 
 
 The tactic [auto] is able to solve a goal that can be proved
    using a sequence of [intros], [apply], [assumption], and [reflexivity].
     The strategy of [auto] consists of trying all
    of the possibilities (using a depth-first search exploration).
 
    The tactic [auto] is simply defined as a shorthand for [auto 5].

    The behavior of [auto n] can be summarized as follows. It first
    tries to solve the goal using [reflexivity] and [assumption]. If
    this fails, it tries to apply a hypothesis (or a lemma that has
    been registered in the hint database), and this application
    produces a number of sugoals. The tactic [auto (n-1)] is then
    called on each of those subgoals. If all the subgoals are solved,
    the job is completed, otherwise [auto n] tries to apply a
    different hypothesis.

    Due to its depth-first strategy, eauto can get exponentially slower as the 
    depth search increases, even when a short proof exists. 
    In general, to make proof search run reasonably fast, one should avoid 
    using a depth search greater than 5 or 6. 
    
     [auto ]cannot exploit lemmas whose instantiation cannot be directly deduced 
     from the proof goal (typically where there is an essentially exsitentuial variable, 
     and we ween to move to the more expensive [eauto]
    *)