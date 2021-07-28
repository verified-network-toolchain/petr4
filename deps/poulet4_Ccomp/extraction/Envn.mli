open EquivDec

module Env :
 sig
  type ('d, 't) t = ('d * 't) list

  val empty : ('a1, 'a2) t

  val find : 'a1 coq_EqDec -> 'a1 -> ('a1, 'a2) t -> 'a2 option

  val bind : 'a1 -> 'a2 -> ('a1, 'a2) t -> ('a1, 'a2) t

  val keys : 'a1 coq_EqDec -> ('a1, 'a2) t -> 'a1 list
 end
