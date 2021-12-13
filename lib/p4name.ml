open Sexplib.Conv
open P4string

type 'a pre_t =
  [%import:'a Poulet4.Typed.name
    [@with Poulet4.P4String.t := P4string.pre_t]]
  [@@deriving sexp,show,yojson]

type t = Info.t pre_t
  [@@deriving sexp,show,yojson]

let to_bare : t -> t = function
  | BareName n
  | QualifiedName (_, n) -> BareName n

let name_info name : Info.t =
  match name with
  | BareName name -> name.tags
  | QualifiedName (prefix, name) ->
     let infos = List.map (fun x -> x.tags) prefix in
     List.fold_right Info.merge infos name.tags

let name_eq n1 n2 =
  match n1, n2 with
  | BareName s1,
    BareName s2 ->
     s1.str = s2.str
  | QualifiedName ([], s1),
    QualifiedName ([], s2) ->
     s1.str = s2.str
  | _ -> false

let name_only n =
  match n with
  | BareName s -> s.str
  | QualifiedName (_, s) -> s.str
