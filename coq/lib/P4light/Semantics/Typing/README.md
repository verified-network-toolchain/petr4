# P4light Type System

This is a **semantic** type-system:
progress & preservation **is** the definition
of a well-typed term (`Typing.v`).

An `Inductive` big-step definition in `Semantics.v`
has a corresponding typing definition in `Typing.v`.
For instance, `exec_expr` has `expr_types`,
`exec_stmt` has `stmt_types`, etc.

The rules of inference are represented as
a `Theorem` rather than a variant in an `Inductive` (`Rules.v`).

## Tour

- `IsTerm.v`: Predicates for well-formed `p4light` programs.
- `Lemmas.v`: Helper lemmas for proving the typing rules.
- `Ok.v`: Predicates that type-variables are bound in a `p4light` term.
- `Rules.v`: Rules of inference as theorems for various `p4light` terms.
- `Typing.v`: Definitions of progress and preservation
for the big-step evaluation in `Semantics.v`.
- `Utility.v`: Helper definitions & lemmas for the type system.
- `ValueTyping.v`: Well-typed `p4light` values.