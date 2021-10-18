# `P4cub`: A Simplified, Stateless `p4` IR

### Contents:

- `P4cub/Syntax`: Abstract-syntax & auxilary definitions.

- `P4cub/Static`: Static semantics, including typechecking.

- `P4cub/Architecture`: The representation of packets, targets, externs, & pipeline.
**UPDATE**: will be repaced entirely by `p4light`'s `Target.v` via translations to and from requisite data types.

- `P4cub/BigStep`: Big-step evaluation semantics.

- `P4cub/SmallStep`: Small-step evaluation semantics.

- `P4cub/Util`: Utility operations, notations, lemmas, & tactics.

- `Envn.v`: Generic notion of environments for `p4cub` semantics.

- `Metamorphosis.v`: Translation from "simplified" `p4light` syntax to `p4cub`.
**UPDATE**: This will be replaced by another translation defined in branch `ec-vcgen`.

- `README.md`: This file :).

### Updates:

- Type variables & specialization are now supported in `p4cub`.

### Goals:

- A verified semantics-preserving translation from `p4cub` to `p4automaton`.

- A fully specified static and dynamic semantics, both big-step and small-step.

- Proven type-soundness theorems, particularly progress and preservation.

- Proven equivalence between big-step and small-step semantics.

- A verified semantics-preserving translation from `p4light` to `p4cub`.

### TODOs:

- `p4cub` Notations are messy and need to be edited and refactored

- Many results in `p4cub` have become invalidated by the introduction of type variables.
This should not pose too large of a problem to resolve.

- Use of induction within induction needs to stop in `p4cub` proofs.

- The core codebase for `p4cub` packets/target/architecture representaion should exist within one directory.

- Constructor parameters currently do nothing for externs. Maybe `p4cub` externs need not have them?

- Explore common ground between `p4light` & `p4cub` architecture/target/packet models.
**UPDATE**: `p4cub` will use `p4light`'s `Target.v` with translations between the requisite data types.
