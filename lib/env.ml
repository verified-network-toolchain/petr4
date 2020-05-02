open Typed
open Prog
open Value
open Core_kernel
open Sexplib.Conv

exception BadEnvironment of string
exception UnboundName of string

type 'binding env = (string * 'binding) list list [@@deriving sexp,yojson]

let push (env: 'a env) : 'a env = [] :: env

let no_scopes () =
  raise (BadEnvironment "no scopes")

let pop: 'a env -> 'a env = function
  | []        -> no_scopes ()
  | _ :: env' -> env'

let rec insert (name: string) (value: 'a) : 'a env -> 'a env = function
  | []     -> no_scopes ()
  | h :: t ->
    try
      if List.Assoc.mem h ~equal:(=) name
      then ((name, value) :: h) :: t
      else h :: (insert name value t)
    with BadEnvironment _ -> ((name, value) :: h) :: t

let insert_firstlevel (name : string) (value : 'a) : 'a env -> 'a env = function
  | [] -> no_scopes ()
  | h :: t -> ((name, value) :: h) :: t

let insert_toplevel (name: string) (value: 'a) (env: 'a env) : 'a env =
  let (env0,env1) = List.split_n env (List.length env - 1) in
  let env1' = insert name value env1 in
  env0 @ env1'

let rec find_opt (name: string) : 'a env -> 'a option = function
  | [] -> None
  | h :: t ->
    let select (name', _) = name = name' in
    match List.find ~f:select h with
    | None              -> find_opt name t
    | Some (_, binding) -> Some binding

let rec find_all (name: string) : 'a env -> 'a list = function
  | [] -> []
  | h :: t ->
     let select acc (name', value) =
       if name' = name
       then value :: acc
       else acc
     in
     List.fold h ~init:[] ~f:select @ find_all name t

let opt_to_exn name v =
  match v with
  | Some v -> v
  | None -> raise (UnboundName name)

let find (name: string) (env: 'a env) : 'a =
  opt_to_exn name (find_opt name env)

let find_toplevel (name: string) (env: 'a env) : 'a = match List.rev env with
  | []       -> no_scopes ()
  | env :: _ -> find name [env]

let find_toplevel_opt (name: string) (env: 'a env) : 'a option = match List.rev env with
| []       -> None
| env :: _ -> find_opt name [env]

let empty_env : 'a env = [[]]

module EvalEnv = struct
  type t = {
    (* the program (top level declarations) so far *)
    decl : Declaration.t env;
    (* maps variables to their values *)
    vs : value env;
    (* map variables to their types; only needed in a few cases *)
    typ : Type.t env;
  }

  let empty_eval_env = {
    decl = [[]];
    vs = [[]];
    typ = [[]];
  }

  let get_toplevel (env : t) : t =
    let get_last l =
      match List.rev l with
      | [] -> raise (BadEnvironment "no toplevel")
      | h :: _ -> [h] in
    {decl = get_last env.decl;
     vs = get_last env.vs;
     typ = get_last env.typ;}

  let get_val_firstlevel env =
    List.hd_exn (env.vs)

  let insert_val name binding e =
    {e with vs = insert name binding e.vs}

  let insert_decl name binding e =
    {e with decl = insert name binding e.decl}

  let insert_typ name binding e =
    {e with typ = insert name binding e.typ}

  let insert_vals bindings e =
    List.fold_left bindings ~init:e ~f:(fun a (b,c) -> insert_val b c a)

  let insert_decls bindings e =
    List.fold_left bindings ~init:e ~f:(fun a (b,c) -> insert_decl b c a)

  let insert_typs bindings e =
    List.fold_left bindings ~init:e ~f:(fun a (b,c) -> insert_typ b c a)

  let find_val name e =
    find name e.vs

  let find_decl name e =
    find name e.decl

  let find_typ name e =
    find name e.typ

  let insert_val_toplevel name v env =
    {env with vs = insert_toplevel name v env.vs}

  let find_val_toplevel name e =
    find_toplevel name e.vs

  let find_decl_toplevel name e =
    find_toplevel name e.decl

  let find_typ_toplevel name e =
    find_toplevel name e.typ

  let insert_val_firstlevel s v e =
    {e with vs = insert_firstlevel s v e.vs}

  let insert_decl_firstlevel s v e =
    {e with decl = insert_firstlevel s v e.decl}

  let insert_typ_firstlevel s v e =
    {e with typ = insert_firstlevel s v e.typ}

  let push_scope (e : t) : t =
    {decl = push e.decl;
     vs = push e.vs;
     typ = push e.typ;}

  let pop_scope (e:t) : t =
    {decl = pop e.decl;
     vs = pop e.vs;
     typ = pop e.typ;}

  (* TODO: for the purpose of testing expressions and simple statements only*)
  let print_env (e:t) : unit =
    let open Core_kernel in
    print_endline "First environment value mappings:";
    let rec f (name, value) =
      print_string "     ";
      print_string name;
      print_string " -> ";
      let vstring = match value with
        | VNull -> "null"
        | VBool b -> string_of_bool b
        | VInteger v
        | VBit {v;_}
        | VInt {v;_}
        | VVarbit {v;_} -> begin match Bigint.to_int v with
            | None -> "<bigint>"
            | Some n -> string_of_int n end
        | VString s -> s
        | VTuple _ -> "<tuple>"
        | VSet _ -> "<set>"
        | VError s -> "Error: " ^ s
        | VMatchKind s -> "Match Kind: " ^ s
        | VFun _ -> "<function>"
        | VBuiltinFun _ -> "<function>"
        | VAction _ -> "<action>"
        | VStruct {fields;_} ->
          print_endline "<struct>";
          List.iter fields ~f:(fun a -> print_string "    "; f a); ""
        | VHeader {fields;is_valid;_} ->
          print_endline ("<header> with " ^ (string_of_bool is_valid));
          List.iter fields ~f:(fun a -> print_string "    "; f a); ""
        | VUnion {valid_header;valid_fields} ->
          print_endline "<union>";
          f ("valid header", valid_header);
          List.iter valid_fields ~f:(fun (a, b) -> print_string "     ";
                           print_string a;
                           print_string " -> ";
                           print_string (string_of_bool b)); ""
        | VStack _ -> "<stack>"
        | VEnumField{typ_name;enum_name} -> typ_name ^ "." ^ enum_name
        | VSenumField{typ_name;enum_name;_} -> typ_name ^ "." ^ enum_name ^ " <value>"
        | VRuntime r -> "<location>"
        | VParser _ -> "<parser>"
        | VControl _ -> "<control>"
        | VPackage _ -> "<package>"
        | VTable _ -> "<table>"
        | VExternFun _ -> "<function>" in
      print_endline vstring in
    match e.vs with
    | [] -> ()
    | h :: _ -> h |> List.rev |> List.iter ~f:f

end

module CheckerEnv = struct

  type t =
    { (* types that type names refer to (or Typevar for vars in scope) *)
      typ: Typed.Type.t env;
      (* maps variables to their types & directions *)
      typ_of: (Typed.Type.t * Typed.direction) env;
      (* maps constants to their values *)
      const: value env }
  [@@deriving sexp,yojson]

  let empty_t : t =
    { typ = empty_env;
      typ_of = empty_env;
      const = empty_env }

  let resolve_type_name_opt name env =
    find_opt name env.typ

  let resolve_type_name name env =
    opt_to_exn name (resolve_type_name_opt name env)

  let resolve_type_name_toplevel name env =
    find_toplevel name env.typ

  let resolve_type_name_toplevel_opt name env =
    find_toplevel_opt name env.typ

  let find_type_of_opt name env =
    find_opt name env.typ_of

  let find_type_of name env =
    opt_to_exn name (find_type_of_opt name env)

  let find_types_of name env =
    find_all name env.typ_of

  let find_type_of_toplevel name env =
    find_toplevel name env.typ_of

  let find_type_of_toplevel_opt name env =
    find_toplevel_opt name env.typ_of

  let find_const name env =
    find name env.const

  let find_const_opt name env =
    find_opt name env.const

  let insert_type name typ env =
    { env with typ = insert_firstlevel name typ env.typ }

  let insert_types names_types env =
    let go env (name, typ) =
      insert_type name typ env
    in
    List.fold ~f:go ~init:env names_types

  let insert_type_var var env =
    { env with typ = insert_firstlevel var (Typed.Type.TypeName var) env.typ }

  let insert_type_vars vars env =
    let go env var =
      insert_type_var var env
    in
    List.fold ~f:go ~init:env vars

  let insert_type_of var typ env =
    { env with typ_of = insert_firstlevel var (typ, Typed.Directionless) env.typ_of }

  let insert_type_of_toplevel var typ env =
    { env with typ_of = insert_toplevel var (typ, Typed.Directionless) env.typ_of }

  let insert_dir_type_of var typ dir env =
    { env with typ_of = insert_firstlevel var (typ, dir) env.typ_of }

  let insert_const var value env =
    { env with const = insert var value env.const }

  let push_scope env =
    { typ = push env.typ;
      typ_of = push env.typ_of;
      const = push env.const }

  let pop_scope env =
    { typ = pop env.typ;
      typ_of = pop env.typ_of;
      const = pop env.const }

  let eval_env_of_t (cenv: t) : EvalEnv.t =
    { decl = [[]];
      vs = cenv.const;
      typ = [[]];}
end
