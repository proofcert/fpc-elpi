List of current examples:

## Property-based testing:
 -- all to be called by dep_pbt. Old examples with pbt are under non-dep
### Completed examples
- `list.v`: some definitions of list predicate (insert, ordered, reverse)

- `list-queries.v`: various properties.

- `aexp.v`: static and dynamic semantics of an arithmetical language (adapted
by `SF/Types.v`), with properties such as preservation, progress,
determinacy. Some mutations are introduced that falsifies those properties.

- `iaexp.v`: same language, but intrinsically typed, so that terms depend on their
type. Preservation is implicit, so we check determinacy, since even for
progress it is hard to write mutants.

### In progress

- `cfg.v` Encoding of contect free grammar. `mut1-cfg.v` is the bugged
version. Currently not working due to Coq-Elpi not supporting mutually
inductive definitions.

- `TImp.v`: initial porting of a typed version of a while language with big step
operational semantics. Property is totality (what?). It's a benchmark for
QuickChick, but makes little sense for us. We could turn it small step.

## Proof reconstruction
- `dd_fpc.v` proves some simple lemmas using as certificate the maximum number of decide-left rules.
- `deb_fpc.v` uses lambda terms with De Brujin indexes as certificates.