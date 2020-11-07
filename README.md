# FPC-Elpi [![Build Status](https://travis-ci.com/proofcert/fpc-elpi.svg)](https://travis-ci.com/proofcert/fpc-elpi)

This repository contains a development that integrates the Foundational Proof
Certificate (FPC) framework into the Coq proof assistant by way of ELPI, an
embeddable λProlog interpreter.

## Description

To prove a given theorem in Coq is to find an inhabitant (i.e, a proof term) of
the type prescribed by the statement of the theorem. Such a construction is
typically achieved by the use of tactics and the built-in Ltac language.

Here we propose a principled alternative to the problem of proof
search and reconstruction in Coq. The *foundational proof certificate*
(FPC) framework can be used to define a wide array of formats for
proof evidence in a communicable and independent manner. A user may
then write or import their own specialized FPCs and use them as
tactics inside Coq, providing a programmable and rigorous alternative
to the often ad hoc process of proof automation.

## Prerequisites

The development depends on the following software. We have tested the following
combinations of package versions, which we recommend installing through the
OPAM package manager, using the standard [OCaml OPAM
repository](https://opam.ocaml.org/) as well as the official [Coq OPAM
repository](https://coq.inria.fr/opam/released/).

`coq` 8.11.0

- `coq-elpi` 1.6.0

- `elpi` 1.11.2

These toolchains should work with recent versions of OCaml (between 4.05.0 and
4.10.0).

Support to use FPC-Elpi interactively is offered by either the Coq toplevel or
the Visual Studio Code editor with `vscoq`, `Elpi lang` and `Coq Elpi lang` addons
installed.

## Examples

The main entry point is file `coq_fpc.v`. In it we define a number of
tactics for intuitionistic formulas in Coq-Elpi using the FPC definitions
contained in the homonymous `fpc` directory:

- A tactic that looks for proofs that take up to a given number of decide
  rules.

- A tactic that looks for proofs guided by lambda term certificates expressed
  in de Bruijn format.

For each of these, a collection of theorems shows how each of the defined
tactics acts on the goal of the theorem and solves it by using the information
provided in the certificate associated to the corresponding FPC format.

## References

A two-page extended abstract describing this project is available as 
*FPC-Coq: Using ELPI to elaborate external proof evidence into Coq
proofs* by Roberto Blanco, Matteo Managhetti, and Dale Miller.  This
[draft](http://www.lix.polytechnique.fr/Labo/Dale.Miller/papers/fpccoq-draft.pdf)
is dated 27 April 2020. 

Other related references are listed below.

 1. Roberto Blanco, Zakaria Chihani, and Dale Miller.  Translating
 between implicit and explicit versions of proof.  In Leonardo
 de~Moura, editor, *Automated Deduction (CADE 26)*, LNCS 10395, pages
 255--273. Springer, 2017. http://doi.org/10.1007/978-3-319-63046-5_16. 

 2. Zakaria Chihani, Dale Miller, and Fabien Renaud.  A semantic
 framework for proof evidence.  *J. of Automated Reasoning*,
 59(3):287--330, 2017. https://doi.org/10.1007/s10817-016-9380-6.

 3. Cvetan Dunchev, Ferruccio Guidi, Claudio~Sacerdoti Coen, and
 Enrico Tassi.  ELPI: fast, embeddable, λProlog interpreter.  In
 Martin Davis, Ansgar Fehnker, Annabelle McIver, and Andrei Voronkov,
 editors, *Logic for Programming, Artificial Intelligence, and
 Reasoning (LPAR-20)*, LNCS 9450, pages
 460--468. Springer, 2015. http://dx.doi.org/10.1007/978-3-662-48899-7_32.

 4. Ferruccio Guidi, Claudio~Sacerdoti Coen, and Enrico Tassi.
 Implementing type theory in higher order constraint logic
 programming.  *Mathematical Structures in Computer Science*,
 29(8):1125--1150, 2019. http://dx.doi.org/10.1017/S0960129518000427.

 5. Dale Miller and Gopalan Nadathur.  *Programming with
 Higher-Order Logic*.  Cambridge University Press, June 2012.
  http://doi.org/10.1017/CBO9781139021326.

 6. Enrico Tassi.  Deriving Proved Equality Tests in Coq-Elpi:
 Stronger Induction Principles for Containers in Coq.  In John
 Harrison, John O'Leary, and Andrew Tolmach, editors, *10th
 International Conference on Interactive Theorem Proving (ITP 2019)*,
 LIPIcs 141, pages 29:1--29:18, Dagstuhl, Germany, 2019.
 http://doi.org/10.4230/LIPIcs.ITP.2019.29.

 7. Enrico Tassi.  Coq plugin embedding ELPI. https://github.com/LPCIC/coq-elpi, 2020.
