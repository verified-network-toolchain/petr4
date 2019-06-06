exception BadEnvironment of string
exception UnboundName of string

type checker_env
type eval_env

val empty_checker_env : checker_env

val find_decl : string -> checker_env -> Types.Declaration.t
val resolve_type_name_opt : string -> checker_env -> Typed.Type.t option
val resolve_type_name : string -> checker_env -> Typed.Type.t
val find_type_of_opt : string -> checker_env -> Typed.Type.t option
val find_type_of : string -> checker_env -> Typed.Type.t
val find_type_of_toplevel : string -> checker_env -> Typed.Type.t

val insert_decl : Types.Declaration.t -> checker_env -> checker_env
val insert_type : string -> Typed.Type.t -> checker_env -> checker_env
val insert_type_of : string -> Typed.Type.t -> checker_env -> checker_env
val insert_type_var : string -> checker_env -> checker_env
val push_scope : checker_env -> checker_env
val pop_scope : checker_env -> checker_env

val eval_env_of_checker_env : checker_env -> eval_env
