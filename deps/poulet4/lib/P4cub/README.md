# `P4cub`: A Simplified, Stateless `p4` IR

### Contents:

- `P4cub/Syntax`: abstract-syntax & auxilary definitions.

- `P4cub/Static`: static semantics, including typechecking.

- `P4cub/P4Packet`: the representation of packets.

- `P4cub/BigStep`: big-step evaluation semantics.

- `P4cub/SmallStep`: small-step evaluation semantics.

### Updates:

- The entire `P4cub` directory is being restructured as its codebase expands.

- An experimental representation of target architectures, `P4cub/Architecture.v` is now used in the big-step semantics. It is primarily used to dispatch `extern` method calls.

- Packets now exist in `p4cub`, & are threaded through the big-step semantics.

### Goals:

- A verified semantics-preserving translation from `p4cub` to `p4automaton`.

- A fully specified static and dynamic semantics, both big-step and small-step.

- Proven type-soundness theorems, particularly progress and preservation.

- Proven equivalence between big-step and small-step semantics.

- A verified semantics-preserving translation from `p4light` to `p4cub`.

### TODOs:

- `record` should be renamed `struct`.

- The file names are verbose, need to resolve an issue with the build so files in different directories may have the same name.

- Many utility definitions & theorems should be moved into separate files, including but not limited to those of `Syntax/AST.v`, `Static/Check.v`, `SmallStep/SSSemantics.v`.

- The core codebase for `p4cub` packets/target/architecture representaion should exist within one directory.

- `BigStep/BSSemantics.v` requires corrections with proper threading of closure environments.

- There need to be closure envrionments for extern instances. There is a potential circular-dependency issue that must be resolved between `BigStep/BSUtil.v` & `BigStep/BSPacket.v`

- The small-step semantics have yet to undergo the comprehensive restructurings that the big-step semantics have.

- Explore common ground between `p4light` & `p4cub` architecture/target/packet models.
