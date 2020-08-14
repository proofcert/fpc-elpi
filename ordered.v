From elpi Require Import elpi.
Require Import Arith List. Import ListNotations.
Require Import Coq.Lists.List.

Inductive ordered : list nat -> Prop :=
	onl : ordered []
  | oss : forall x : nat, ordered [x]
  | ocn : forall (x y : nat) (l : list nat),
         ordered (y :: l) -> x <= y -> ordered (x :: y :: l)
.
Elpi Command pbt.
Elpi Accumulate File "pbt/src/kernel.mod".
Elpi Typecheck.
Fail Elpi Query lp:{{
  interp {{ordered [1;0;2].}}.
  }}.

Elpi Query lp:{{
  interp {{ordered [1;1;2].}}.
  }}.

Elpi Query lp:{{
coq.locate "le" (indt LE), coq.env.indt LE _ _ _ T C Ts.
}}.

Elpi Query lp:{{
  coq.locate "ordered" GR,   coq.say "ordered is:" GR,
  coq.env.typeof GR Ty, coq.say "The type of ordered is:" Ty.  
}}.

Elpi Query lp:{{
    coq.locate "ordered" (indt GR),
    coq.env.indt GR _ _ _ Type Kn Types.   % get the names of the constructors
 }}.
