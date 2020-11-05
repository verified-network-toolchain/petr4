# Refactoring the AST

1. Remove mutual recursion where possible
  - Put env into its own module
  - Get rid of DeclarationStatements
  - make lvalue index have type nat, rather than Value [Ryan]
2. Remove dependencies on Types AST
  - Types.Expression in Annotation
  - Types.Expression in Parameter default values [Ryan]
3. Assert_* functions from Prog should be monadic functions in their own module
   [Molly]
  - Example https://github.com/cornell-netlab/poulet4/blob/master/lib/Eval.v#L61-L65
4. PPX annotations have to be added
5. Fix representation of environments
6. Use control-plane names for controllable entities
7. Provide "arbitrary annotations" rather than having annotations and info on
   every syntax node.
   - Inductive AST  := | Add : AST -> AST -> AST | Var : string -> AST
   - Inductive AST (X:Type) := Add : X -> AST -> AST -> AST
                             | Var : X -> string -> AST
   - Definition AST_with_info := AST Info.t
   - Definition AST_with_info_and_type := AST (Info.t * Typed.Type.t)
   - AST (Info * Type) -> AST (Info * Type * Set Var)
   - UntypedAST (Info * Annotation) -> TypedAST (Info * Annotation * Type)
8. Better names (e.g., `Stat_BlockStatement` should be `StmtBlock` and let's
   not mix CamelCase and underscore_separated_words) [Molly]
9. Stratify types [Molly]
10. Make externs nominal [Ryan]
11. Inline constants with a constant folding pass after typechecker and before
    Coq, remove const declarations [Ryan]

# Refactoring the interpreter
- [ ] Repair evaluator to handle indirect storage of packets
- [ ] Parametrize over targets with typeclasses the way the OCaml version uses
      modules

# Questions

1. Can we avoid having info in our Coq code while still having it in OCaml
