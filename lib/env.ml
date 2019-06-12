open Error
open Types
open Typed
open Env

type 'binding env = (P4String.t * 'binding) list list

type t =
  { exp: (ExpType.t * direction) env ;
    typ: ExpType.t env;
    decl: DeclType.t  env;
    value: Value.t env; }

let empty_env = {
  exp   = [[]];
  typ   = [[]];
  decl  = [[]];
  value = [[]];
}

let raise_missing () =
  raise (Internal "missing top-level environment")

let push env = [] :: env

let pop = function
  | []        -> raise_missing ()
  | _ :: []   -> raise (Internal "popping top-level environment")
  | _ :: env' -> env'

let insert name binding = function
  | []     -> raise_missing ()
  | h :: t -> ((name, binding) :: h) :: t

let insert_toplevel name binding env =
  env |> List.rev
  |> insert name binding
  |> List.rev

let rec good_find name env = 
  Core.List.find_exn env ~f:(fun ((_,name'),_) -> name' = snd name)

let rec find name = function
  | []     ->
    let (info, name) = name in
    raise (Type (info, Unbound name))
  | h :: t ->
    let select ((_, name'), _) = snd name = name' in
    match List.find_opt select h with
    | None              -> find name t
    | Some (_, binding) -> binding


let find_toplevel name env = match List.rev env with
  | []       -> raise_missing ()
  | env :: _ -> find name [env]

let rec contains (typ: ExpType.t) (name: P4String.t)= function
  | [] -> false
  | h :: t ->
    let eq = fun ((_, name'), (typ', _)) -> snd name = name' && typ = typ' in
    if List.exists eq h then true else contains typ name t

let contains_toplevel (typ: ExpType.t) (name: P4String.t) env =
  match List.rev env with
  | []       -> raise_missing ()
  | env :: _ -> contains typ name [env]
