# `P4cub`: A Simplified, Stateless `p4` IR

### Updates:

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
