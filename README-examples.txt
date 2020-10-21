List of current examples:

list.v: some definitions of list predicate (insert, ordered, reverse)

	list-queries.v: various properties, to be called both by pbt *and* dep_pbt

aexp.v: static and dynamic semantics of an arithmetical language
(adapted by SF/Types.v), with properties such as preservation,
progress, determinacy. Some mutations are introduced that falsifies
those properties.

iaexp.v: same language, but intrinsically typed, so that terms depend
on their type. Preservation is implicit, so we check determinacy,
since even for progress it is hard to write mutants.

cfg. Encoding of contect free grammar. mut1-cfg.v is the buged version. Mutually inductive,
weird stuff happening.

TImp.v: initial porting of a typed version of a while language with big step operational semantics. Property is totality (what?). It's a benchmark for QuickChick, but makes little sense for us. We could turn it small step. In progress.
