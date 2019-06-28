open Types
open Value

exception BadEnvironment of string
exception UnboundName of string

module EvalEnv : sig
  type t

  val empty_eval_env : t

  val get_toplevel : t -> t
  val get_val_firstlevel : t -> (string * value) list

  val insert_val : string -> value -> t -> t
  val insert_decl: string -> Declaration.t -> t -> t
  val insert_typ : string -> Type.t -> t -> t
  val insert_err : string -> t -> t

  val insert_vals : (string * value) list -> t -> t
  val insert_decls: (string * Declaration.t) list -> t ->t
  val insert_typs : (string * Type.t) list -> t -> t
  val insert_errs : string list -> t ->t 

  val find_val : string -> t -> value
  val find_decl: string -> t -> Declaration.t
  val find_typ : string -> t -> Type.t
  val find_err : string -> t -> value

  val find_val_toplevel : string -> t -> value
  val find_decl_toplevel: string -> t -> Declaration.t
  val find_typ_toplevel : string -> t -> Type.t

  val push_scope : t -> t
  val pop_scope : t -> t

  val print_env : t -> unit
end

module CheckerEnv : sig
  type t

  val empty_checker_env : t

  val find_decl : string -> t -> Types.Declaration.t
  val resolve_type_name_opt : string -> t -> Typed.Type.t option
  val resolve_type_name : string -> t -> Typed.Type.t
  val find_type_of_opt : string -> t -> (Typed.Type.t * Typed.direction) option
  val find_type_of : string -> t -> Typed.Type.t * Typed.direction
  val find_type_of_toplevel : string -> t -> Typed.Type.t * Typed.direction

  val insert_decl : Types.Declaration.t -> t -> t
  val insert_type : string -> Typed.Type.t -> t -> t
  val insert_type_of : string -> Typed.Type.t -> t -> t
  val insert_type_of_toplevel : string -> Typed.Type.t -> t -> t
  val insert_dir_type_of : string -> Typed.Type.t -> Typed.direction -> t -> t
  val insert_type_var : string -> t -> t
  val push_scope : t -> t
  val pop_scope : t -> t

  val eval_env_of_checker_env : t -> EvalEnv.t
end
