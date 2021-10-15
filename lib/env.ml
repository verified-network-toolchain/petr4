module I = Info
open Core_kernel
module Info = I
let (=) = Stdlib.(=)
let (<>) = Stdlib.(<>)

exception BadEnvironment of string
exception UnboundName of string
exception AlreadyBound of string

let mk_unbound (name: P4name.t) : exn =
  let str_name =
    match name with
    | QualifiedName (qs, name) ->
      List.map ~f:(fun s -> s.str) qs @ [name.str]
      |> String.concat ~sep:"."
    | BareName name ->
       name.str
  in
  UnboundName str_name

let mk_already_bound (name: P4name.t) : exn =
  let str_name =
    match name with
    | QualifiedName (qs, name) ->
      List.map ~f:(fun s -> s.str) qs @ [name.str]
      |> String.concat ~sep:"."
    | BareName name ->
       name.str
  in
  AlreadyBound str_name

type 'binding t = (string * 'binding) list list [@@deriving sexp,show,yojson]

let push (env: 'a t) : 'a t = [] :: env

let no_scopes () =
  raise (BadEnvironment "no scopes")

let pop: 'a t -> 'a t = function
  | []        -> no_scopes ()
  | _ :: env' -> env'

let split_at (name: string) scope =
  let rec split_at' seen scope =
    match scope with
    | [] -> None
    | (x, value) :: rest ->
       if x = name
       then Some (seen, (x, value), rest)
       else split_at' (seen @ [x, value]) rest
  in
  split_at' [] scope

let update_in_scope name value scope =
  match split_at name scope with
  | None -> None
  | Some (xs, _, ys) ->
     Some (xs @ (name, value) :: ys)

let insert_bare name value env =
  match env with
  | [] -> no_scopes ()
  | h :: t -> ((name, value) :: h) :: t

let rec update_bare name value env =
  match env with
  | [] -> no_scopes ()
  | inner_scope :: scopes ->
     match update_in_scope name value inner_scope with
     | Some inner_scope -> Some (inner_scope :: scopes)
     | None ->
        match update_bare name value scopes with
        | Some env -> Some (inner_scope :: env)
        | None -> None

let update_toplevel name value env =
  let (env0,env1) = List.split_n env (List.length env - 1) in
  match update_bare name value env1 with
  | Some env1' -> Some (env0 @ env1')
  | None -> None

let insert_toplevel (name: string) (value: 'a) (env: 'a t) : 'a t =
  let (env0,env1) = List.split_n env (List.length env - 1) in
  let env1' = insert_bare name value env1 in
  env0 @ env1'

let update (name: P4name.t) (value: 'a) (env: 'a t) : 'a t option =
  match name with
  | BareName name -> update_bare name.str value env
  | QualifiedName ([], name) -> update_toplevel name.str value env
  | _ -> failwith "unimplemented"

let rec find_bare_opt (name: string) : 'a t -> 'a option =
  function
  | [] -> None
  | h :: t ->
     let select (name', _) = name = name' in
     match List.find ~f:select h with
     | None              -> find_bare_opt name t
     | Some (_, binding) -> Some binding

let rec find_all_bare (name: string) : 'a t -> 'a list =
  function
  | [] -> []
  | h :: t ->
     let f acc (name', value) =
       if name' = name
       then value :: acc
       else acc
     in
     List.fold h ~init:[] ~f @ find_all_bare name t

let find_all (name: P4name.t) (env: 'a t) : 'a list =
  match name with
  | BareName name -> find_all_bare name.str env
  | QualifiedName ([], n) ->
     begin match List.last env with
     | Some top -> find_all_bare n.str [top]
     | None -> no_scopes ()
     end
  | _ -> failwith "unimplemented"

let opt_to_unbound name =
  Util.opt_to_exn (mk_unbound name)

let find_bare (name: string) (env: 'a t) : 'a =
  let bare_name: P4name.t = BareName {tags = Info.dummy; str = name} in
  opt_to_unbound bare_name @@ find_bare_opt name env

let find_toplevel (name: string) (env: 'a t) : 'a =
  match List.rev env with
  | []       -> no_scopes ()
  | env :: _ -> find_bare name [env]

let find_toplevel_opt (name: string) (env: 'a t) : 'a option =
  match List.rev env with
  | []       -> None
  | env :: _ -> find_bare_opt name [env]

let find (name: P4name.t) (env: 'a t) : 'a =
  match name with
  | BareName n -> find_bare n.str env
  | QualifiedName ([], n) -> find_toplevel n.str env
  | _ -> failwith "unimplemented"

let find_opt (name: P4name.t) (env: 'a t) : 'a option =
  match name with
  | BareName n -> find_bare_opt n.str env
  | QualifiedName ([], n) -> find_toplevel_opt n.str env
  | _ -> failwith "unimplemented"

let present (name: P4name.t) (env: 'a t) : bool =
  match find_opt name env with
  | Some _ -> true
  | None -> false

let insert ?shadow:(shadow=false) (name: P4name.t) (value: 'a) (env: 'a t) : 'a t =
  if not shadow && present name env
  then raise (mk_already_bound name)
  else match name with
       | BareName name ->
          insert_bare name.str value env
       | QualifiedName ([], name) ->
          insert_toplevel name.str value env
       | _ -> failwith "unimplemented"

let empty_env : 'a t = [[]]
