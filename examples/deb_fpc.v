From elpi Require Import elpi.
Require Import coq_fpc.

Goal forall P: Prop, P -> P.
elpi deb_fpc 1.
Qed.

Goal forall P Q: Prop, Q -> (P -> P).
elpi deb_fpc 2.
Qed.

Goal forall P Q: Prop, (P -> Q) -> (P -> Q).
elpi deb_fpc 3.
Qed.

Goal forall P Q: Prop, (P -> (Q -> ((P -> P) -> P))).
elpi deb_fpc 4.
Qed.

Goal forall P Q R: Prop, (P -> ((((P -> Q) -> Q) -> R) -> R)).
elpi deb_fpc 5.
Qed.

Goal forall P Q R: Prop, (P -> ((((Q -> P) -> P) -> R) -> R)).
elpi deb_fpc 6.
Qed.

Theorem dneg_exc_mid : forall P Q : Prop, ((P -> Q) -> ((P -> Q) -> Q) -> Q).
Proof. elpi deb_fpc 7. Qed.

Theorem dneg_peirce_mid : forall P Q: Prop, (((((P -> Q) -> P) -> P) -> Q) -> Q).
Proof. elpi deb_fpc 8. Qed.