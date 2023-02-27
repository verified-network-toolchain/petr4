# `P4cub`: A Simplified, Stateless `p4` IR

### Contents:

- `ExportAll.v`: Exports (nearly) everything in this directory.

- `Semantics`: Static & Dynamic semantics including type system, big-step evaluation,
  small-step evaluation, & type-soundness properties.

- `Syntax`: `p4cub` syntax and auxiliary definitions, notations, equality, and induction principles.

- `Transformations`: `p4cub` to `p4cub` transformations including
  lifting, constant folding, and correctness proofs.

- `README.md`: This file :).

### Updates:

- `p4cub` now uses de Bruijn indices for type and term variables!

### Goals:

- A verified semantics-preserving translation from `p4cub` to `clight`.

- A fully specified static and dynamic semantics, both big-step and small-step.

- Proven type-soundness theorems, particularly progress and preservation.

- Proven equivalence between big-step and small-step semantics.

- A verified semantics-preserving translation from `p4light` to `p4cub`.

- Verify semantics are preserved for `p4cub` to `p4cub` transformations.

### TODOs:

- `p4cub` will use `p4light`'s `Target.v` with translations between the requisite data types.
  Need to connect `p4cub` dynamic semantics to `Target.v`

- Prove correctness of compiler transformations.

- Complete type-soundness proofs.
