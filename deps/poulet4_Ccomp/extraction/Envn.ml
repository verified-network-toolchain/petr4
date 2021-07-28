open EquivDec

module Env =
 struct
  type ('d, 't) t = ('d * 't) list

  (** val empty : ('a1, 'a2) t **)

  let empty =
    []

  (** val find : 'a1 coq_EqDec -> 'a1 -> ('a1, 'a2) t -> 'a2 option **)

  let rec find hE x = function
  | [] -> None
  | p :: e' -> let (y, v) = p in if hE x y then Some v else find hE x e'

  (** val bind : 'a1 -> 'a2 -> ('a1, 'a2) t -> ('a1, 'a2) t **)

  let bind x v e =
    (x, v) :: e

  (** val keys : 'a1 coq_EqDec -> ('a1, 'a2) t -> 'a1 list **)

  let rec keys hE = function
  | [] -> []
  | p :: e' ->
    let (y, _) = p in
    let keys' = keys hE e' in
    (match find hE y e' with
     | Some _ -> keys'
     | None -> y :: keys')
 end
