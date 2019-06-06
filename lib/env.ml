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

let insert_toplevel (name: string) (binding: 'a) (env: 'a env) : 'a env =
  env |> List.rev
      |> insert name binding
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

type type_name_meaning =
| TypeVar
| TypeRef of Typed.Type.t

type checker_env =
  { (* the program (top level declarations) so far *)
    decl: Types.Declaration.t list;
    (* types that type names refer to (or Typevar for vars in scope) *)
    typ: type_name_meaning env;
    (* maps variables to their types & directions *)
    typ_of: (Typed.Type.t * Typed.direction) env;
    (* maps constants to their values *)
    const: Value.t env; }

let empty_checker_env : checker_env =
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
  { env with typ = insert name (TypeRef typ) env.typ }

let insert_type_var var env =
  { env with typ = insert var TypeVar env.typ }

let insert_type_of var typ env =
  { env with typ_of = insert var (typ, Typed.Directionless) env.typ_of }

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

type eval_env =
  { (* the program (top level declarations) so far *)
    decl: Types.Declaration.t list;
    (* maps variables to their values *)
    var: Value.t env; }

let eval_env_of_checker_env (cenv: checker_env) : eval_env =
  { decl = cenv.decl;
    var = cenv.const }
