open BinPos
open Datatypes

module N :
 sig
  val succ_double : Bigint.t -> Bigint.t

  val double : Bigint.t -> Bigint.t

  val add : Bigint.t -> Bigint.t -> Bigint.t

  val sub : Bigint.t -> Bigint.t -> Bigint.t

  val compare : Bigint.t -> Bigint.t -> comparison

  val leb : Bigint.t -> Bigint.t -> bool

  val log2 : Bigint.t -> Bigint.t

  val pos_div_eucl : Bigint.t -> Bigint.t -> Bigint.t * Bigint.t

  val div_eucl : Bigint.t -> Bigint.t -> Bigint.t * Bigint.t

  val to_nat : Bigint.t -> int
 end
