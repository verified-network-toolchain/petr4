open Types
open Typed

val type_expression: Env.CheckerEnv.t -> Expression.t -> Type.t

val type_statement: Env.CheckerEnv.t -> Statement.t -> (StmType.t * Env.CheckerEnv.t)

val type_declaration: Env.CheckerEnv.t -> Declaration.t -> Env.CheckerEnv.t

val check_program : Types.program -> Env.CheckerEnv.t
