# `P4cub`: A Simplified, Stateless `p4` IR

### Goals:

- A fully specified static and dynamic semantics, both big-step and small-step.

- Proven type-soundness theorems, particularly progress and preservation.

- Proven equivalence between big-step and small-step semantics.

- A verified semantics-preserving translation from `p4light` to `p4cub`.

### TODOs:

- Explore better ways to enfore constructions of types with proper nesting.

- Use `Z` instead of `N` (Currently doing this). `positive` will NOT be replaced with `nat`?

- Usurp `P4cub/P4Arith.v` with p4light's arithmetic operations.

- Disallow non-constant global variable declarations in `AST.v`.

- Use `p4light` architecture model/type-class in dynamic semantics.
