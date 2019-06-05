open Types
open Typed

val type_expression: Env.checker_env -> Expression.t -> Type.t

val type_statement: Env.checker_env -> Statement.t -> (StmType.t * Env.checker_env)

val type_declaration: Env.checker_env -> Declaration.t -> Env.checker_env

val type_type_declaration: Env.checker_env -> TypeDeclaration.t -> Env.checker_env

val check_program : Types.program -> Env.checker_env
