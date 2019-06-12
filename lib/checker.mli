open Types
open Typed

val type_expression: Env.t -> Expression.t -> ExpType.t

val type_statement: Env.t -> Statement.t -> (StmType.t * Env.t)

val type_declaration: Env.t -> Declaration.t -> Env.t

val type_type_declaration: Env.t -> TypeDeclaration.t -> Env.t

val check_program : Types.program -> Env.t
