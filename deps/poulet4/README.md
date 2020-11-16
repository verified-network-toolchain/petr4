# Refactoring the AST

1. Remove mutual recursion where possible
  - [ ] Put env into its own module
  - [x] Get rid of DeclarationStatements
  - [x] make lvalue index have type nat, rather than Value [Ryan]
2. Remove dependencies on Types AST
  - [ ] turn @optional annotations into a boolean in Parameter [Ryan]
  - [ ] remove Annotation from AST and only define it in OCaml [Ryan]
  - [ ] Types.Expression in Parameter default values [Ryan]
3. [x] Assert_* functions from Prog should be monadic functions in their own module
   [Molly]
  - [x] Example https://github.com/cornell-netlab/poulet4/blob/master/lib/Eval.v#L61-L65
4. Get the OCaml to build with the current Coq AST [Ryan]
  - [ ] PPX annotations have to be added
5. [ ] Fix representation of environments
6. [ ] Use control-plane names for controllable entities
7. [x] Provide "arbitrary annotations" rather than having annotations
   and info on every syntax node.
   - Go from this:

      Inductive AST  :=
      | Add : AST -> AST -> AST
      | Var : string -> AST

   - To this:

      Inductive AST (X:Type) :=
      | Add : X -> AST -> AST -> AST
      | Var : X -> string -> AST

   - then we have

      Definition AST_with_info := AST Info.t
      Definition AST_with_info_and_type := AST (Info.t * Typed.Type.t)

8. [x] Better names (e.g., `Stat_BlockStatement` should be `StmtBlock` and let's
   not mix CamelCase and underscore_separated_words) [Molly]
9. [ ] Stratify types into 3 parts [Ryan]
10. [ ] Make externs nominal [Ryan]
11. [ ] Stratify values into 3 parts [Molly]

# Refactoring the interpreter
- [ ] Repair evaluator to handle indirect storage of packets
- [ ] Parametrize over targets with typeclasses the way the OCaml version uses
      modules

# Other things
1. Don't bother with type syntactic equality functions, leave them to OCaml
   since they're only used in the typechecker
   - Maybe revisiting the typing of table entries can fix this
   - better representation for contents of tables?

# Questions

1. Can we avoid having info in our Coq code while still having it in OCaml
