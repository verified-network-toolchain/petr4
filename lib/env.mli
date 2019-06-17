exception BadEnvironment of string
exception UnboundName of string

type checker_env [@@deriving sexp]
type eval_env [@@deriving sexp]

val empty_checker_env : checker_env

val all_decls : checker_env -> Types.Declaration.t list
val find_decl : string -> checker_env -> Types.Declaration.t
val resolve_type_name_opt : string -> checker_env -> Typed.Type.t option
val resolve_type_name : string -> checker_env -> Typed.Type.t
val resolve_type_name_toplevel : string -> checker_env -> Typed.Type.t
val find_type_of_opt : string -> checker_env -> (Typed.Type.t * Typed.direction) option
val find_type_of : string -> checker_env -> Typed.Type.t * Typed.direction
val find_type_of_toplevel : string -> checker_env -> Typed.Type.t * Typed.direction

val insert_decl : Types.Declaration.t -> checker_env -> checker_env
val insert_type : string -> Typed.Type.t -> checker_env -> checker_env
val insert_type_of : string -> Typed.Type.t -> checker_env -> checker_env
val insert_type_of_toplevel : string -> Typed.Type.t -> checker_env -> checker_env
val insert_dir_type_of : string -> Typed.Type.t -> Typed.direction -> checker_env -> checker_env
val insert_type_var : string -> checker_env -> checker_env
val push_scope : checker_env -> checker_env
val pop_scope : checker_env -> checker_env

val eval_env_of_checker_env : checker_env -> eval_env
