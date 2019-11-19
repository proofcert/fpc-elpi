From elpi Require Import elpi.

Module Type LKF_Params.

  (* Predicate symbols *)
  Parameter Prd     : Set.
  Parameter Prd_eqb : Prd -> Prd -> bool.

  (* Constants *)
  Parameter Fun     : Set.
  Parameter Fun_eqb : Fun -> Fun -> bool.

End LKF_Params.

Module LKF (Params : LKF_Params).

  Import Params.

  (* Terms *)
  Inductive Tm : Set :=
  | Var : nat -> Tm
  | App : Fun -> list Tm -> Tm
  .

  (* Polarity *)
  Inductive Pol : Set :=
  | Positive : Pol
  | Negative : Pol
  .

  (* Polarized formulas *)
  Inductive Form : Set :=
  | Atom  : Pol -> Prd -> list Tm -> Form
  | And   : Pol -> Form -> Form -> Form
  | True  : Pol -> Form
  | Or    : Pol -> Form -> Form -> Form
  | False : Pol -> Form
  | Quant : Pol -> (Tm -> Form) -> Form
  .

  (* De Morgan duality *)

  Fixpoint dual_pol (p : Pol) : Pol :=
    match p with
    | Positive => Negative
    | Negative => Positive
    end.

  Fixpoint dual (f : Form) : Form :=
    match f with
    | Atom p a ts => Atom (dual_pol p) a ts
    | And p f1 f2 => Or (dual_pol p) (dual f1) (dual f2)
    | True p      => False (dual_pol p)
    | Or p f1 f2  => And (dual_pol p) (dual f1) (dual f2)
    | False p     => True (dual_pol p)
    | Quant p f   => Quant (dual_pol p) (fun t => dual (f t))
    end.

  (* Sequents *)

  Inductive SeqKind : Set := Unf | Foc.
  Inductive Sequent : Set :=
  | Seq : SeqKind -> nat -> list Form -> list Form -> Sequent.

  (* Certificates *)

  Inductive Choice : Set :=
  | ChLeft : Choice
  | ChRight : Choice
  .

  Inductive Cert : Set :=
  | C0 : Cert                         (* nullary *)
  | C1 : Cert -> Cert                 (* unary *)
  | C2 : Cert -> Cert -> Cert         (* binary *)
  | Ch : Choice -> Cert -> Cert       (* choice *)
  | Cx : nat -> Cert                  (* index *)
  | Cd : nat -> Cert -> Cert          (* decision *)
  | Ce : (Tm -> Cert) -> Cert         (* eigen *)
  | Cw : Tm -> Cert -> Cert           (* witness *)
  | Ct : Form -> Cert -> Cert -> Cert (* cut *)
  .

End LKF.

Module TestParams <: LKF_Params.
  Definition Fun := nat.
  Definition Fun_eqb := Nat.eqb.

  Definition Prd := nat.
  Definition Prd_eqb := Nat.eqb.
End TestParams.

Module LKF_Test := LKF (TestParams).
Import TestParams LKF_Test.

Elpi Command fpc.
Elpi Accumulate File "coq-fpc.mod".
Elpi Query "example 1 X Y.".
Elpi Query "hope 1.".
Elpi Query "maximize 2 (max X C).".
Elpi Query "example 1 Tm Ty, debi 0 Tm Deb, polarize- Ty Form, ljf_entry ((lc 0 Deb) <c> (max _ M)) Form.".
Elpi Accumulate File "maximal-fpc.mod".
Elpi Accumulate File "pairing-fpc.mod".
Elpi Query "maximize 2 (max X Y).".
Elpi Query "hope 2.".
Elpi Query "maximize 2 (max zero C), max->coq C D.".