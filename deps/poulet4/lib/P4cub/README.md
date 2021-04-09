# `P4cub`: A Simplified, Stateless `p4` IR

### Goals:

- A fully specified static and dynamic semantics, both big-step and small-step.

- Proven type-soundness theorems, particularly progress and preservation.

- Proven equivalence between big-step and small-step semantics.

- A verified semantics-preserving translation from `p4light` to `p4cub`.

### TODOs:

- Currently removing `tags_t` from `p4cub` types and values. Such "info" annotations shall henceforth exists only explicitly in `p4cub` syntax.

- Removing all uses of `P4String.t` and qualified names from `Typed.v`, locators will be used instead.

- Usurp `P4cub/P4Arith.v` with p4light's arithmetic operations.

- Disallow non-constant global variable declarations in `AST.v`.

- Use `p4light` architecture model/type-class in dynamic semantics.
