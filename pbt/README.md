## Prerequisites

The development contained in the [source folder](src/) is written in the λProlog
programming language. It occasionally relies on advanced features available only
in [ELPI](https://github.com/LPCIC/elpi), though most of the development runs
without modification on [Teyjus](https://github.com/teyjus/teyjus/) as well.

## Repository structure

The root contains a proof checking kernel and proof certificate definitions for
property-based testing in the FPC framework. The certificates enable exhaustive
and random counterexample search and are applied to a range of examples, each
located in its own sub-folder with core definitions, correct and buggy variants
of some of these, and top-level files packaging all those together into full
programs and their associated test cases (these top-level files generally have
the word `bug` in their names).

## Running the tests

For example, consider the [first bug](src/Stlc/stlc-bug1.mod) in the [test
suite](src/Stlc/) of the simply-typed lambda calculus example. Load the `.mod`
file in ELPI including the requisite folders, namely the root where the common
modules are located and the concrete sub-folder for the example:

    $ elpi -I src/ -I src/Stlc stlc-bug1.mod

At the prompt, enter a goal to try to find a counterexample to a given property.
For the STLC example, a [dedicated module](src/Stlc/stlc-tests.sig) defines
predicates for the various properties of interest and for the term generation
strategies under consideration. For example, to try to obtain a counterexample
to the progress property using exhaustive generation of terms of gradually
increasing height:

    goal> cexprog_h E T.

Upon success, the system will output a term `E` of type `T` that fails to
satisfy this property.
