(*

- make the arguments uniform in the call to the tactic ????

ex: 
(dep)_prolog  N: call with height default
             size/pair N M:

something similar with pbt             

-------------------------
can we preprocess the constructors of Inductive
with copy, so that we put them n "clausal" forms, by removing
the Coq quantifiers? Then we can remove backchaining altoghether.



Elpi tactic takes the conjecture in it's orifinal form
and it is disproved, we abort. This makes sense, but
in reality we are proving a theorem, namely its negation.

If Elpi fails, the trace is kernel is not displayed
-----------------------


-----------------------------------
- should we do dep products in check as well? [done]
---------------------
- on generation: feeding the right term, the query does work

- lack of indexing: to prove 1 <= 10 we do 21 backchaining
steps, since we always try x <= x first. At worst
if we have k constructors, when prolog would take n steps
we take n * k.

==> this seems different from the standard prog thing

prog (le X X) true
prog (le X (s Y)) (le X Y),

which index on the first argument of prog and would take 11 steps 

==> could we preprocess (viz. build_clauses in pbt.v) the inductive def
turning parameters into logic variables and then use lprolog
indexing? 


----------------------------
kernel.mod:

the axiom and pi-left rule assume that Ctx contains at most one formula.
This may hold in our application, but is generally false -- 
just try check _ [] (prod _ T (prod  : T T))

why has pi-right a clerk and left an expert? Just terminology

check could be written hypothetically as hyp/conc

But why not have backchain eben in check ? Why we need the context? why pi-right?

[action: move to back-chain based version of check,
think about better use of dependent types later]
----------------------------
OLD(ish)
In PPDP19 there is a clear correspondence between the sequent calculus (fig 4) and
the implementation of check (fig 5) and interp (fig.9). Lacking that
I have trouble following the implementation and my observations maybe be completely off

- the proof theury behibf interp and check should be the same, except that check 
threads the certificate along. However, they are now quite different, as far as rules are concerned
(minor point:  we have interp {{nat}} but not check for that)

- the pi left/right rule have no expert; same for init. Is that intended? 
Why is it different from say the and-right rule?

- the proof term of pi left is puzzling (I was expecting an application), as well as the fact that it is linear
in the assumptions: there is no general Ctx,  and prod is not contracted. By reference
here is a left rule for -> with proof terms from Pfenning's notes

Γ, u:A ⊃ B ⇒ J : A
Γ, u:A ⊃ B, w:B ⇒ I : C
------------------------------
Γ, u:A ⊃ B ⇒ [u J/w]I : C

- not sure why we need to put an atom in whd in unfold
[BTW, in the elpi documentation it says

% Note that the solve goal is not under a context containg the decl/def
% entries.  It is up to the user to eventually load the context as follows
%  solve _ [goal Ctx _ Ty] _ :- Ctx => unwind {whd Ty []} WhdTy.]

- I don't understand the unfold rule fully, but two things are worrying me:
1. it's very inefficient, since we are not doing indexing on the goalwhile selecting
the clause to match -- it seems we pick them chrologiavlly and try them in order
2. we should not be in the business of checking that 0 is a nat or [0] is a nat list
(it's like doing dynamic typing, which is ironic in Coq)
, 
- how do we write tactic pbt so that is
checks preconditions and interp negation of conclusion?

- pbt sould actually be called "chk" for fpc driven
lp and keep pbt the whole thing

-
Could we write check hypothetically instead of a explicit Ctx

How we we know that Term : Type (in Coq?) or coq.typecheck Term Type  if
check etc is provable?

- check Cert [A] A (fun _ A (x\x)).

 => should it be more general?

 check Cert L A (fun _ A (x\x)) :- memb A L.

 => should there be a axiom expert?


*)


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

(* lp casts term into whatever, eg Prop

{{_}} quote a Coq exp into "term"
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