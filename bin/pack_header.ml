module type Map = sig
  type ('k, 'v) t
  val insert : 'k -> 'v -> ('k, 'v) t -> ('k, 'v) t
  val find : 'k -> ('k, 'v) t -> 'v option
  val empty : ('k, 'v) t 
end

module AssocListMap : Map = struct
  type ('k, 'v) t = ('k * 'v) list
  let insert k v m = (k, v) :: m
  let find = List.assoc_opt
  let empty = []
end
let pack= AssocListMap.empty
