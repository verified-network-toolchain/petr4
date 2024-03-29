# `P4cub` Big-step Dynamic Semantics

### Modules:

- `BigStep.v`: Exports all modules in this directory.

- `Determinism.v`: Proofs that big-step evaluation as defined in `Semantics.v` is deterministic.

- `ExprUtil.v`: Utility operations & type-soundness lemmas for operators in `p4cub`.

- `IndPrincip.v`: Induction principles for the evaluation relations in `Semantics.v`.

- `Semantics.v`: Big-step evaluation in `p4cub`.

- `TypeSoundness.v`: Proofs of progress & preservation for big-step evaluation.

- `ValEnvUtil.v`: Definitions of operators for value environments, such as lookup, update, copy-in & copy-out.