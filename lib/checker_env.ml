module I = Info
open Core_kernel
module Info = I

type t =
  { (* types that type names refer to (or Typevar for vars in scope) *)
    typ: P4light.coq_P4Type Env.t;
    (* maps variables to their types & directions *)
    typ_of: (P4light.coq_P4Type * P4light.direction) Env.t;
    (* maps constants to their values *)
    const: P4light.coq_Value Env.t;
    (* maps default expr ids to expressions *)
    default_args: Surface.Expression.t list ref;
    (* externs *)
    externs: P4light.coq_ExternMethods Env.t;
    (* for generating fresh type variables *)
    renamer: Renamer.t ref;
  }

let empty_with_renamer r : t =
  { typ = Env.empty_env;
    typ_of = Env.empty_env;
    const = Env.empty_env;
    default_args = ref [];
    externs = Env.empty_env;
    renamer = r }

let top_scope env : t =
  { typ = [List.last_exn env.typ];
    typ_of = [List.last_exn env.typ_of];
    const = [List.last_exn env.const];
    default_args = env.default_args;
    externs = [List.last_exn env.externs];
    renamer = env.renamer }

let empty_t () : t =
  empty_with_renamer @@ ref (Renamer.create ())

let renamer env =
  !(env.renamer)

let push_scope (env: t) : t =
  { typ = Env.push env.typ;
    typ_of = Env.push env.typ_of;
    const = Env.push env.const;
    default_args = env.default_args;
    externs = Env.push env.externs;
    renamer = env.renamer }

let resolve_type_name_opt (name : P4string.t) env =
  Env.find_bare_opt name.str env.typ

let resolve_type_name (name : P4string.t) env =
  Util.opt_to_exn (Env.UnboundName name.str)
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

let insert_type ?shadow:(shadow=false) name typ env =
  { env with typ = Env.insert ~shadow name typ env.typ }

let insert_types ?shadow:(shadow=false) names_types env =
  let go env (name, typ) =
    insert_type ~shadow (BareName name) typ env
  in
  List.fold ~f:go ~init:env names_types

let insert_type_var var env =
  let typ: P4light.coq_P4Type = TypTypeName var in
  { env with typ = Env.insert_bare var.str typ env.typ }

let insert_type_vars vars env =
  let go env var = insert_type_var var env in
  List.fold ~f:go ~init:env vars

let insert_dir_type_of ?shadow:(shadow=false) var typ dir env =
  { env with typ_of = Env.insert ~shadow var (typ, dir) env.typ_of }

let insert_type_of ?shadow:(shadow=false) var typ env =
  insert_dir_type_of ~shadow var typ Directionless env

let insert_const var value env =
  { env with const = Env.insert ~shadow:false var value env.const }

let add_default_arg expr env =
  let l = !(env.default_args) in
  env.default_args := l @ [expr];
  List.length l

let insert_extern var value env =
  { env with externs = Env.insert ~shadow:false var value env.externs }
