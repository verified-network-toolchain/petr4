open BinPosDef
open Datatypes
open Nat

module Pos :
 sig
  val succ : Bigint.t -> Bigint.t

  val add : Bigint.t -> Bigint.t -> Bigint.t

  val add_carry : Bigint.t -> Bigint.t -> Bigint.t

  val pred_double : Bigint.t -> Bigint.t

  type mask = Pos.mask =
  | IsNul
  | IsPos of Bigint.t
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : Bigint.t -> mask

  val sub_mask : Bigint.t -> Bigint.t -> mask

  val sub_mask_carry : Bigint.t -> Bigint.t -> mask

  val size : Bigint.t -> Bigint.t

  val compare_cont : comparison -> Bigint.t -> Bigint.t -> comparison

  val compare : Bigint.t -> Bigint.t -> comparison

  val iter_op : ('a1 -> 'a1 -> 'a1) -> Bigint.t -> 'a1 -> 'a1

  val to_nat : Bigint.t -> int
 end
