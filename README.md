# FPC-Elpi

This repository contains a development that integrates the Foundational Proof
Certificate (FPC) framework into the Coq proof assistant by way of ELPI, an
embeddable λProlog interpreter.

## Description

To prove a given theorem in Coq is to find an inhabitant (i.e, a proof term) of
the type prescribed by the statement of the theorem. Such a construction is
typically achieved by the use of tactics and the built-in Ltac language.

Here we propose a principled alternative to the problem of proof search and
reconstruction in Coq. We know that proof certificates (FPCs) can be used to
define a wide array of formats for proof evidence in a communicable and
independent manner. A user may then write or import their own specialized FPCs
and use them as tactics inside Coq, providing a programmable and rigorous
alternative to the often ad hoc process of proof automation.

## Prerequisites

The development depends on the following software. We have tested the following
combinations of package versions, which we recommend installing through the
OPAM package manager, using the standard [OCaml OPAM
repository](https://opam.ocaml.org/) as well as the official [Coq OPAM
repository](https://coq.inria.fr/opam/released/).

- `coq` 8.11.0

- `coq-elpi` 1.3.1

- `elpi` 1.10.2

Either the Coq toplevel or an interactive editor like Visual Studio Code with
Coq and ELPI addons installed can be used.

## Examples

The main entry point is file `coq_fpc_dep.v`. In it we define a number of
tactics for intuitionistic formulas in Coq-Elpi using the FPC definitions
contained in the homonymous `fpc` directory:

- A tactic that looks for proofs that take up to a given number of decide
  rules.

- A tactic that looks for proofs guided by lambda term certificates expressed
  in de Bruijn format.

For each of these, a collection of theorems shows how each of the defined
tactics acts on the goal of the theorem and solves it by using the information
provided in the certificate associated to the corresponding FPC format.
