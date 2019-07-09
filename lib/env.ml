open Types
open P4core
open Value
open Core

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
    match List.find ~f:select h with
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
    decl : Declaration.t env;
    (* maps variables to their values *)
    vs : value env;
    (* map variables to their types; only needed in a few cases *)
    typ : Types.Type.t env;
    (* the error namespace *)
    err : string list;
    (* the parser error *)
    parser_error : string
  }

  let empty_eval_env = {
    decl = [[]];
    vs = [[]];
    typ = [[]];
    err = [];
    parser_error = "NoError";
  }

  let get_toplevel (env : t) : t =
    let get_last l =
      match List.rev l with
      | [] -> raise (BadEnvironment "no toplevel")
      | h :: _ -> [h] in
    {decl = get_last env.decl;
     vs = get_last env.vs;
     typ = get_last env.typ;
     err = env.err;
     parser_error = env.parser_error;}

  let get_val_firstlevel env =
    List.hd_exn (env.vs)

  let insert_val name binding e =
    {e with vs = insert name binding e.vs}

  let insert_decl name binding e =
    {e with decl = insert name binding e.decl}

  let insert_typ name binding e =
    {e with typ = insert name binding e.typ}

  let insert_err name e =
    {e with err = name :: e.err}

  let insert_vals bindings e =
    List.fold_left bindings ~init:e ~f:(fun a (b,c) -> insert_val b c a)

  let insert_decls bindings e =
    List.fold_left bindings ~init:e ~f:(fun a (b,c) -> insert_decl b c a)

  let insert_typs bindings e =
    List.fold_left bindings ~init:e ~f:(fun a (b,c) -> insert_typ b c a)

  let insert_errs ss e =
    {e with err = e.err @ ss}

  let find_val name e =
    find name e.vs

  let find_decl name e =
    find name e.decl

  let find_typ name e =
    find name e.typ

  let find_err name e =
    if List.exists ~f:(fun a -> a = name) e.err
    then VError name
    else raise (UnboundName name)

  let find_val_toplevel name e =
    find_toplevel name e.vs

  let find_decl_toplevel name e =
    find_toplevel name e.decl

  let find_typ_toplevel name e =
    find_toplevel name e.typ

  let set_error (s : string) (env : t) : t =
    {env with parser_error = s}

  let get_error (env : t) : string =
    env.parser_error

  let push_scope (e : t) : t =
    {decl = push e.decl;
     vs = push e.vs;
     typ = push e.typ;
     err = e.err;
     parser_error = e.parser_error;}

  let pop_scope (e:t) : t =
    {decl = pop e.decl;
     vs = pop e.vs;
     typ = pop e.typ;
     err = e.err;
     parser_error = e.parser_error;}

  (* TODO: for the purpose of testing expressions and simple statements only*)
  let print_env (e:t) : unit =
    let open Core in
    print_endline "First environment value mappings:";
    let rec f (name, value) =
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
        | VError _ -> "<error>"
        | VMatchKind -> "<matchkind>"
        | VFun _ -> "<function>"
        | VBuiltinFun _ -> "<function>"
        | VAction _ -> "<action>"
        | VStruct (_, l) ->
          print_endline "<struct>";
          List.iter l ~f:(fun a -> print_string "    "; f a); ""
        | VHeader (_,l,b) ->
          print_endline ("<header> with " ^ (string_of_bool b));
          List.iter l ~f:(fun a -> print_string "    "; f a); ""
        | VUnion (_,l,v) ->
          print_endline "<union>";
          f ("valid header", l);
          List.iter v ~f:(fun (a, b) -> print_string "     ";
                           print_string a;
                           print_string " -> ";
                           print_string (string_of_bool b)); ""
        | VStack _ -> "<stack>"
        | VEnumField(enum,field) -> enum ^ "." ^ field
        | VSenumField(enum,field,_) -> enum ^ "." ^ field ^ " <value>"
        | VExternFun _ -> "<extern function>"
        | VExternObject _ -> "<extern>"
        | VRuntime _ -> "packet"
        | VObjstate (_,vs) -> "<stateful object>" in
      print_endline vstring in
    match e.vs with
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
    match List.find ~f:ok env.decl with
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
      vs = cenv.const;
      typ = [[]];
      err = [];
      parser_error = "NoError"}
end
