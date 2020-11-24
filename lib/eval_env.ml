open Typed
open Core_kernel

type t = {
    (* maps variables to their locations in memory (state) *)
    vs : string Env.t;
    (* map variables to their types; only needed in a few cases *)
    typ : coq_P4Type Env.t;
    (* dynamically maintain the control-plane namespace *)
    namespace : string;
  }

let empty_eval_env = {
    vs = [[]];
    typ = [[]];
    namespace = "";
  }

let get_val_firstlevel (env: t) =
  match env.vs with
  | scope :: rest -> scope
  | [] -> Env.no_scopes ()

let get_toplevel (env : t) : t =
  let get_last l =
    match List.rev l with
    | [] -> raise @@ Env.BadEnvironment "no toplevel"
    | h :: _ -> [h] in
  {vs = get_last env.vs;
   typ = get_last env.typ;
   namespace = "";}

let get_val_firstlevel env =
  List.hd_exn (env.vs)

let get_namespace env =
  env.namespace

let set_namespace name env =
  {env with namespace = name}

let insert_val name binding e =
  {e with vs = Env.insert name binding e.vs}

let insert_val_bare name binding e =
  {e with vs = Env.insert (Typed.BareName name) binding e.vs}

let insert_typ name binding e =
  {e with typ = Env.insert name binding e.typ}

let insert_typ_bare name =
  insert_typ (Typed.BareName name)

let insert_vals bindings e =
  List.fold_left bindings ~init:e ~f:(fun a (b,c) -> insert_val b c a)

let fix_bindings bindings =
  List.map bindings
    ~f:(fun (name, v) -> Typed.BareName name, v)

let insert_vals_bare bindings =
  insert_vals (fix_bindings bindings)

let insert_typs bindings e =
  List.fold_left bindings ~init:e ~f:(fun a (b,c) -> insert_typ b c a)

let insert_typs_bare bindings =
  insert_typs (fix_bindings bindings)

let find_val name e =
  Env.find name e.vs

let find_val_opt name e =
  Env.find_opt name e.vs

let find_typ name e =
  Env.find name e.typ

let push_scope (e : t) : t =
  {vs = Env.push e.vs;
   typ = Env.push e.typ;
   namespace = e.namespace;}

let pop_scope (e:t) : t =
  {vs = Env.pop e.vs;
   typ = Env.pop e.typ;
   namespace = e.namespace;}
