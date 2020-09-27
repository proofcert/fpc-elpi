From elpi Require Import elpi.
Require Import Arith List. Import ListNotations.
Require Import Coq.Lists.List.


Elpi Tactic pbt.
Elpi Accumulate File "pbt/src/kernel.mod".
Elpi Accumulate File "pbt/src/fpc-qbound.mod".

Elpi Query lp:{{
    coq.locate "le" (indt GR),
    coq.env.indt GR _ _ _ Type Kn Types.   % get the names of the constructors
 }}.

Elpi Query lp:{{
  interp {{ 0 <= 5}}.
  }}.

Elpi Accumulate lp:{{
  solve [int N] [goal Ctx Ev Ty _] [] :-
    check (qgen (qheight N)) [] Ty,
    coq.say "Ottenuto" Ty.
}}.
Elpi Typecheck.

 Inductive ordered : list nat -> Prop :=
	onl : ordered []
  | oss : forall x : nat, ordered [x]
  | ocn : forall (x y : nat) (l : list nat),
         ordered (y :: l) -> x <= y -> ordered (x :: y :: l).

(* the following is the bugged version*)
Inductive ordered_bad : list nat -> Prop :=
   onlb : ordered_bad []
  | ossb : forall x : nat, ordered_bad [x]
  | ocnb : forall (x y : nat) (l : list nat),
                ordered_bad l  -> x <= y -> ordered_bad (x:: y :: l).         

Hint  Constructors ordered : core.
Hint Constructors list : core .

(*
Goal ordered [0;0].
elpi pbt 10.
Qed.

Goal ordered [1;2;3;4;5;5;12;13].
elpi pbt 20.
Qed.
*)

Inductive insert (x : nat) : list nat -> list nat -> Prop:=
 | inil: insert  x [] [x]
 |ic1 : forall y ys, x <= y -> insert x (y :: ys) (x :: y :: ys)
 |ic2: forall y ys ns, y < x -> insert x ys ns ->  insert x (y :: ys) (y :: ns).

 Hint  Constructors insert.
 Goal exists L, insert 3 ( 1 :: 2 :: nil) L.
 eauto 10.
  Qed.
  
  (* this should be provable*)
  Conjecture pres: forall x xs ys, ordered ys -> insert x xs ys -> ordered ys.
  (* this is false and we should get a cex*)
  Conjecture pres_bad: forall x xs ys, ordered_bad ys -> insert x xs ys -> ordered_bad ys.

  (* pres_bad negated, knowing the cex already*)
  Goal exists x xs ys, ordered_bad xs /\ insert x xs ys /\ not (ordered_bad ys).
exists 0.
exists [0;1;0].
eexists. split.
- constructor. constructor. auto.
- econstructor. econstructor. auto.
intro. inversion H; subst; clear H.
inversion H4; subst; clear H4.
inversion H2; subst; clear H2.
inversion H4.
Qed.



Inductive natlist : list nat -> Prop :=
natn : natlist []
| natc : forall (x  : nat) (l : list nat),
       natlist l  -> natlist (x :: l).


(*the PBT query with manual generator: loops for now*)
Elpi Query lp:{{
  check (qgen (qheight 4)) [] {{natlist lp:Xs /\ ordered_bad lp:Xs.}},
  interp {{insert 0 lp:Xs lp:Rs.}}, 
  not (interp {{ordered_bad lp:Rs.}}).
  }}.


(*the PBT query, cheating: *)
Elpi Query lp:{{
  check (qgen (qheight 4)) [] {{ordered_bad [0;1;0].}},
  interp {{insert lp:X [0;1;0] lp:Rs.}}, 
  not (interp {{ordered_bad lp:Rs.}}).
  }}.



Elpi Query lp:{{
	check  (qgen (qheight 4)) {{ (ordered [1;2]).}}.       
  }}.
Elpi Query lp:{{
  coq.locate "ordered" (indt LE), coq.env.indt-decl LE X.
}}.


Elpi Query lp:{{
  interp {{ 1 <= 2}}.
  }}.

Fail Elpi Query lp:{{
  interp {{ordered [1;0;2].}}.
  }}.

Elpi Query lp:{{
  interp {{ordered [1;1;2].}}.
  }}.

Elpi Query lp:{{
  not (interp {{ordered [1;0;2].}}).
  }}.

Elpi Query lp:{{
  interp {{ 1 <= 22}}.
  }}.

Elpi Query lp:{{
  interp {{ 1 = 1}}.
  }}.

(* we don't do reflexivity yet*)
Fail Elpi Query lp:{{
  interp {{ 1 = (0 + 1)}}.
  }}.

(* comparison with auto*)
Goal 1 <= (22 + 1).
simpl.
auto 25.
Qed.
 
  (* auto here fails without the right bound, but vanilla has no problem*)  
    Goal
    True /\ True /\ True /\ True /\ True /\ True.
  Proof.
    auto.
    Restart.
    auto 6.
  Qed.   

  Elpi Query lp:{{
  interp {{True /\ True  /\ True /\ True /\ True.}}.
  }}.


(* what about gvar? *)
Elpi Query lp:{{
  interp {{ordered lp: Xs.}}.
  }}. 

Elpi Query lp:{{
	check  (qgen (qheight 4)) {{ (ordered [1;2]).}}.       
  }}.

(* 
Elpi Query lp:{{
coq.locate "le" (indt LE), coq.env.indt LE _ _ _  T C Ts.
}}.


LE: name of indictive
T: its type
C: list of constructors name 
Ts list of constructors: le_n : n <= n is 
(prod `n` (global (indt «nat»)) n \ app [global (indt «le»), n, n]) *)

(*
Elpi Query lp:{{
  coq.locate "ordered" GR,   coq.say "ordered is:" GR,
  coq.env.typeof GR Ty, coq.say "The type of ordered is:" Ty.  
}}.

Elpi Query lp:{{
    coq.locate "ordered" (indt GR),
    coq.env.indt GR _ _ _ Type Kn Types.   % get the names of the constructors
 }}.
*)