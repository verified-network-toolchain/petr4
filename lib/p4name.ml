open Poulet4.Typed

type 'a pre_t = 'a Poulet4.Typed.name

type t = P4info.t pre_t

let to_bare : t -> t = function
  | BareName n
  | QualifiedName (_, n) -> BareName n

let name_tags name : P4info.t =
  match name with
  | BareName name -> name.tags
  | QualifiedName (prefix, name) ->
     let infos = List.map (fun (x: P4string.t) -> x.tags) prefix in
     List.fold_right P4info.merge infos name.tags

let name_eq n1 n2 =
  match n1, n2 with
  | BareName s1,
    BareName s2 ->
     s1.str = s2.str
  | QualifiedName ([], s1),
    QualifiedName ([], s2) ->
     s1.str = s2.str
  | _ -> false

let p4string_name_only n =
  match n with
  | BareName s
  | QualifiedName (_, s) -> s

let name_only n =
  (p4string_name_only n).str

