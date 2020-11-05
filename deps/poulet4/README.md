# Refactoring the AST

1. Remove mutual recursion where possible
  - Put env into its own module
  - Get rid of DeclarationStatements
2. Remove dependencies on Types AST
  - Types.Expression in Annotation
  - Types.Expression in Parameter default values
3. Assert_* functions from Prog should be monadic functions in their own module
  - Example https://github.com/cornell-netlab/poulet4/blob/master/lib/Eval.v#L61-L65
4. PPX annotations have to be added
5. Fix representation of environments
6. Use control-plane names for controllable entities
7. Provide "arbitrary annotations" rather than having annotations and info on
   every syntax node.
8. Better names (e.g., `Stat_BlockStatement` should be `StmtBlock` and let's
   not mix CamelCase and underscore_separated_words)

# Refactoring the interpreter
- [ ] Repair evaluator to handle indirect storage of packets
- [ ] Parametrize over targets with typeclasses the way the OCaml version uses
      modules

# Questions

1. Can we avoid having info in our Coq code while still having it in OCaml
