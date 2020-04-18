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

  val insert_vals : (string * value) list -> t -> t
  val insert_decls: (string * Declaration.t) list -> t ->t
  val insert_typs : (string * Type.t) list -> t -> t

  val find_val : string -> t -> value
  val find_decl: string -> t -> Declaration.t
  val find_typ : string -> t -> Type.t

  val insert_val_toplevel : string -> value -> t -> t

  val find_val_toplevel : string -> t -> value
  val find_decl_toplevel: string -> t -> Declaration.t
  val find_typ_toplevel : string -> t -> Type.t

  val insert_val_firstlevel : string -> value -> t -> t
  val insert_decl_firstlevel: string -> Declaration.t -> t -> t
  val insert_typ_firstlevel : string -> Type.t -> t -> t

  val push_scope : t -> t
  val pop_scope : t -> t

  val print_env : t -> unit
end

module CheckerEnv : sig
  type t [@@deriving sexp,yojson]

  val empty_t : t

  val resolve_type_name_opt : string -> t -> Typed.Type.t option
  val resolve_type_name : string -> t -> Typed.Type.t
  val all_decls : t -> Prog.Declaration.t list
  val find_decl_opt : string -> t -> Prog.Declaration.t option
  val find_decl : string -> t -> Prog.Declaration.t
  val find_type_of_opt : string -> t -> (Typed.Type.t * Typed.direction) option
  val find_type_of : string -> t -> Typed.Type.t * Typed.direction
  val find_types_of : string -> t -> (Typed.Type.t * Typed.direction) list
  val find_type_of_toplevel : string -> t -> Typed.Type.t * Typed.direction

  val insert_type : string -> Typed.Type.t -> t -> t
  val insert_type_of : string -> Typed.Type.t -> t -> t
  val insert_type_of_toplevel : string -> Typed.Type.t -> t -> t
  val insert_dir_type_of : string -> Typed.Type.t -> Typed.direction -> t -> t
  val insert_type_var : string -> t -> t
  val insert_decl : Prog.Declaration.t -> t -> t
  val push_scope : t -> t
  val pop_scope : t -> t

  val resolve_type_name_opt : string -> t -> Typed.Type.t option
  val resolve_type_name : string -> t -> Typed.Type.t
  val resolve_type_name_toplevel : string -> t -> Typed.Type.t
  val resolve_type_name_toplevel_opt : string -> t -> Typed.Type.t option
  val find_type_of_opt : string -> t -> (Typed.Type.t * Typed.direction) option
  val find_type_of : string -> t -> Typed.Type.t * Typed.direction
  val find_type_of_toplevel_opt : string -> t -> (Typed.Type.t * Typed.direction) option
  val find_type_of_toplevel : string -> t -> Typed.Type.t * Typed.direction
  val find_const : string -> t -> value
  val find_const_opt : string -> t -> value option

  val insert_type : string -> Typed.Type.t -> t -> t
  val insert_types : (string * Typed.Type.t) list -> t -> t
  val insert_type_of : string -> Typed.Type.t -> t -> t
  val insert_type_of_toplevel : string -> Typed.Type.t -> t -> t
  val insert_dir_type_of : string -> Typed.Type.t -> Typed.direction -> t -> t
  val insert_type_var : string -> t -> t
  val insert_type_vars : string list -> t -> t
  val insert_const : string -> value -> t -> t
  val push_scope : t -> t
  val pop_scope : t -> t

  val eval_env_of_t : t -> EvalEnv.t
end
