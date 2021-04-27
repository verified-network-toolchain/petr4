# `P4cub`: A Simplified, Stateless `p4` IR

### Contents:

"W/ batteries" implies the inclusion of useful definitions, lemmas, and/or tactics.

- `AST.v`: the `p4cub` abstract syntax tree w/ batteries.

- `BigStep.v`: `p4cub` big-step semantics w/ batteries.

- `Check.v`: `p4cub` static semantics.

- `Field.v`: `p4cub`'s syntactic "fields" w/ batteries.

- `Metamorphosis.v`: Translation from `p4light` to `p4cub`.

- `SmallStep.v`: `p4cub` small-step values/lvalues, & semantics w/ batteries.

- `Utilizer.v`: Useful notations, definitions, lemmas, & tactics.

### Updates:

- Work on translation from `p4light` to `p4cub` has begun.

- All uses of `N` have been usurped by `Z`.

- `p4cub` now uses `lib/P4Arith.v` for unary/binary operations on fixed-width integers.

- `p4cub` supports casts from tuples to records and headers.

- `p4cub` supports bit-slicing.

### Goals:

- A fully specified static and dynamic semantics, both big-step and small-step.

- Proven type-soundness theorems, particularly progress and preservation.

- Proven equivalence between big-step and small-step semantics.

- A verified semantics-preserving translation from `p4light` to `p4cub`.

### TODOs:

- Explore better ways to enfore constructions of types with proper nesting.

- Disallow non-constant global variable declarations in `AST.v`.

- Use `p4light` architecture model/type-class in dynamic semantics.
