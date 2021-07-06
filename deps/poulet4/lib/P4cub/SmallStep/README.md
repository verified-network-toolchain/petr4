# `P4cub` Small-step Dynamic Semantics

### Modules:

- `Determinism.v`: Proofs that evaluation as defined in `Semantics.v` is deterministic.

- `Semantics.v`: Small-step dynamic semantics relations for `p4cub`.

- `SmallStep.v`: Exports all modules in this directory.

- `TypeSoundness.v`: Proofs of progress & preservation of small-step evaluation as in `Semantics.v`.

- `Util.v`: Utility definitions & lemmas for small-step evaluation.

- `Value.v`: Notion of small-step values in `p4cub`, as well as lemmas & tactics for canonical forms.