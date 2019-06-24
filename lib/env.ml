open Types
open Value

exception BadEnvironment of string
exception UnboundName of string

type 'binding env = (string * 'binding) list list

let push (env: 'a env) : 'a env = [] :: env

let no_scopes () =
  raise (BadEnvironment "no scopes")

let pop: 'a env -> 'a env = function
  | []        -> no_scopes ()
  | _ :: env' -> env'

let insert (name: string) (value: 'a) : 'a env -> 'a env = function
  | []     -> no_scopes ()
  | h :: t -> ((name, value) :: h) :: t

let insert_toplevel (name: string) (value: 'a) (env: 'a env) : 'a env =
  env |> List.rev
  |> insert name value
  |> List.rev


let rec find_opt (name: string) : 'a env -> 'a option = function
  | [] -> None
  | h :: t ->
    let select (name', _) = name = name' in
    match List.find_opt select h with
    | None              -> find_opt name t
    | Some (_, binding) -> Some binding

let opt_to_exn name v =
  match v with
  | Some v -> v
  | None -> raise (UnboundName name)

let find (name: string) (env: 'a env) : 'a =
  opt_to_exn name (find_opt name env)

let find_toplevel (name: string) (env: 'a env) : 'a = match List.rev env with
  | []       -> no_scopes ()
  | env :: _ -> find name [env]

let empty_env : 'a env = [[]]

module EvalEnv = struct
  type t = {
    (* the program (top level declarations) so far *)
    decl: Declaration.t env;
    (* maps variables to their values *)
    var: value env;
    (* map variables to their types; only needed in a few cases *)
    typ : Types.Type.t env;
    (* the error namespace *)
    err : string list;
  }

  let empty_eval_env = {
    decl = [[]];
    var = [[]];
    typ = [[]];
    err = [];
  }

  let get_toplevel (env : t) : t =
    let get_last l =
      match List.rev l with
      | [] -> raise (BadEnvironment "no toplevel")
      | h :: _ -> [h] in
    {decl = get_last env.decl;
     var = get_last env.var;
     typ = get_last env.typ;
     err = env.err;}

  let get_decl_toplevel (env : t) : (string * Declaration.t) list =
    match List.rev env.decl with
    | [] -> no_scopes ()
    | h :: _ -> h

  let insert_value (e : t) name binding : t =
    {e with var = insert name binding e.var}

  let insert_decls (e : t) name binding : t =
    {e with decl = insert name binding e.decl}

  let insert_typ e name binding =
    {e with typ = insert name binding e.typ}

  let insert_err e name =
    {e with err = name :: e.err}

  let find_value name e : value =
    find name e.var

  let find_decl name e : Declaration.t =
    find name e.decl

  let find_typ name e = find name e.typ

  let find_err name e =
    if List.mem name e.err then
      VError name
    else
      raise (UnboundName name)

  let find_value_toplevel name e : value =
    find_toplevel name e.var

  let find_decl_toplevel name e : Declaration.t =
    find_toplevel name e.decl

  let find_typ_toplevel name e = find_toplevel name e.typ

  let push_scope (e : t) : t =
    {decl = push e.decl;
     var = push e.var;
     typ = push e.typ;
     err = e.err;}

  let pop_scope (e:t) : t =
    {decl = pop e.decl;
     var = pop e.var;
     typ = pop e.typ;
     err = e.err;}

  (* TODO: for the purpose of testing expressions and simple statements only*)
  let print_env (e:t) : unit =
    let open Core in
    print_endline "First environment value mappings:";
    let f (name, value) =
      print_string "     ";
      print_string name;
      print_string " -> ";
      let vstring = match value with
        | VNull -> "null"
        | VBool b -> string_of_bool b
        | VInteger v
        | VBit(_, v)
        | VInt(_, v) -> begin match Bigint.to_int v with
            | None -> "<bigint>"
            | Some n -> string_of_int n end
        | VTuple _ -> "<tuple>"
        | VSet _ -> "<set>"
        | VString s -> s
        | VError _ -> "<error"
        | VMatchKind -> "<matchkind>"
        | VFun _ -> "<function>"
        | VAction _ -> "<action>"
        | VStruct _ -> "<struct>"
        | VHeader (_,_,b) -> "<header> with " ^ (string_of_bool b)
        | VEnumField (enum,field) -> enum ^ "." ^ field
        | VExternFun _ -> "<extern function>"
        | VExternObject _ -> "<extern>"
        | VObjstate _ -> "<stateful object>" in
      print_endline vstring in
    match e.var with
    | [] -> ()
    | h :: _ -> h |> List.rev |> List.iter ~f:f

end

module CheckerEnv = struct

  type t =
    { (* the program (top level declarations) so far *)
      decl: Types.Declaration.t list;
      (* types that type names refer to (or Typevar for vars in scope) *)
      typ: Typed.Type.t env;
      (* maps variables to their types & directions *)
      typ_of: (Typed.Type.t * Typed.direction) env;
      (* maps constants to their values *)
      const: value env; }

  let empty_checker_env : t =
    { decl = [];
      typ = empty_env;
      typ_of = empty_env;
      const = empty_env; }

  let find_decl name env =
    let ok decl =
      name = snd (Types.Declaration.name decl)
    in
    match List.find_opt ok env.decl with
    | Some v -> v
    | None -> raise (UnboundName name)

  let resolve_type_name_opt name env =
    find_opt name env.typ

  let resolve_type_name name env =
    opt_to_exn name (resolve_type_name_opt name env)

  let find_type_of_opt name env =
    find_opt name env.typ_of

  let find_type_of name env =
    opt_to_exn name (find_type_of_opt name env)

  let find_type_of_toplevel name env =
    find_toplevel name env.typ_of

  let insert_decl d env =
    { env with decl = d :: env.decl }

  let insert_type name typ env =
    { env with typ = insert name typ env.typ }

  let insert_type_var var env =
    { env with typ = insert var (Typed.Type.TypeVar var) env.typ }

  let insert_type_of var typ env =
    { env with typ_of = insert var (typ, Typed.Directionless) env.typ_of }

  let insert_type_of_toplevel var typ env =
    { env with typ_of = insert_toplevel var (typ, Typed.Directionless) env.typ_of }

  let insert_dir_type_of var typ dir env =
    { env with typ_of = insert var (typ, dir) env.typ_of }

  let push_scope env =
    { decl = env.decl;
      typ = push env.typ;
      typ_of = push env.typ_of;
      const = push env.const }

  let pop_scope env =
    { decl = env.decl;
      typ = pop env.typ;
      typ_of = pop env.typ_of;
      const = pop env.const }

  let eval_env_of_checker_env (cenv: t) : EvalEnv.t =
    { decl = [[]];
      var = cenv.const;
      typ = [[]];
      err = [];}
end
