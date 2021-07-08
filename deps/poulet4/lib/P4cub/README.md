# `P4cub`: A Simplified, Stateless `p4` IR

### Contents:

- `P4cub/Syntax`: Abstract-syntax & auxilary definitions.

- `P4cub/Static`: Static semantics, including typechecking.

- `P4cub/Architecture`: The representation of packets, targets, externs, & pipeline.

- `P4cub/BigStep`: Big-step evaluation semantics.

- `P4cub/SmallStep`: Small-step evaluation semantics.

- `Envn.v`: Generic notion of environments for `p4cub` semantics.

- `Metamorphosis.v`: Translation from "simplified" `p4light` syntax to `p4cub`.

- `README.md`: This file :).

- `Utiliser.v`: Utility operations, notations, lemmas, & tactics.

### Updates:

- The entire `P4cub` directory is being restructured as its codebase expands.

- An experimental representation of target architectures, `P4cub/Architecture.v` is now used in the big-step semantics. It is primarily used to dispatch `extern` method calls.

- Packets now exist in `p4cub` & are threaded through the big-step semantics.

### Goals:

- A verified semantics-preserving translation from `p4cub` to `p4automaton`.

- A fully specified static and dynamic semantics, both big-step and small-step.

- Proven type-soundness theorems, particularly progress and preservation.

- Proven equivalence between big-step and small-step semantics.

- A verified semantics-preserving translation from `p4light` to `p4cub`.

### TODOs:

- The core codebase for `p4cub` packets/target/architecture representaion should exist within one directory.

- Constructor parameters currently do nothing for externs. Maybe `p4cub` externs need not have them?

- Explore common ground between `p4light` & `p4cub` architecture/target/packet models.
