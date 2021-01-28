module I = Info
open Core_kernel
module Info = I

exception NameAlreadyBound

type t =
  { (* types that type names refer to (or Typevar for vars in scope) *)
    typ: Typed.coq_P4Type Env.t;
    (* maps variables to their types & directions *)
    typ_of: (Typed.coq_P4Type * Typed.direction) Env.t;
    (* maps constants to their values *)
    const: Prog.coq_Value Env.t;
    (* maps default expr ids to expressions *)
    default_args: Types.Expression.t list ref;
    (* externs *)
    externs: Prog.coq_ExternMethods Env.t;
    (* for generating fresh type variables *)
    renamer: Renamer.t;
  }

let empty_with_renamer r : t =
  { typ = Env.empty_env;
    typ_of = Env.empty_env;
    const = Env.empty_env;
    default_args = ref [];
    externs = Env.empty_env;
    renamer = r }

let empty_t () : t =
  empty_with_renamer @@ Renamer.create ()

let renamer env =
  env.renamer

let resolve_type_name_opt name env =
  Env.find_opt name env.typ

let resolve_type_name name env =
  Env.opt_to_unbound name
    @@ resolve_type_name_opt name env

let find_type_of_opt name env =
  Env.find_opt name env.typ_of

let find_type_of name env =
  Env.opt_to_unbound name @@ find_type_of_opt name env

let find_types_of name env =
  Env.find_all name env.typ_of

let find_const name env =
  Env.find name env.const

let find_const_opt name env =
  Env.find_opt name env.const

let find_default_arg id env =
  List.nth_exn !(env.default_args) id

let find_extern name env =
  Env.find name env.externs

let find_extern_opt name env =
  Env.find_opt name env.externs

let insert_type name typ env =
  { env with typ = Env.insert name typ env.typ }

let insert_types names_types env =
  let go env (name, typ) =
    insert_type (BareName name) typ env
  in
  List.fold ~f:go ~init:env names_types

let insert_type_var var env =
  let typ: Typed.coq_P4Type = TypTypeName var in
  { env with typ = Env.insert var typ env.typ }

let insert_type_vars vars env =
  let go env var = insert_type_var (BareName var) env in
  List.fold ~f:go ~init:env vars

let insert_dir_type_of var typ dir env =
  { env with typ_of = Env.insert var (typ, dir) env.typ_of }

let insert_type_of var typ env =
  insert_dir_type_of var typ Directionless env

let insert_const var value env =
  match find_const_opt var env with
  | Some _ -> raise NameAlreadyBound
  | None -> { env with const = Env.insert var value env.const }

let add_default_arg expr env =
  let l = !(env.default_args) in
  env.default_args := l @ [expr];
  List.length l

let insert_extern var value env =
  match find_extern_opt var env with
  | Some _ -> raise NameAlreadyBound
  | None -> { env with externs = Env.insert var value env.externs }
