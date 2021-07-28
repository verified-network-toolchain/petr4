open Archi
open BinInt
open BinNums
open BinPos
open Binary
open Bits
open Coqlib
open Datatypes
open IEEE754_extra
open Integers
open Zaux
open Zbits

type float = binary64

type float32 = binary32

val cmp_of_comparison : comparison -> Datatypes.comparison option -> bool

val ordered_of_comparison : Datatypes.comparison option -> bool

val quiet_nan_64_payload : positive -> positive

val quiet_nan_64 : (bool * positive) -> float

val default_nan_64 : float

val quiet_nan_32_payload : positive -> positive

val quiet_nan_32 : (bool * positive) -> float32

val default_nan_32 : float32

module Float :
 sig
  val expand_nan_payload : positive -> positive

  val expand_nan : bool -> positive -> binary_float

  val of_single_nan : float32 -> float

  val reduce_nan_payload : positive -> positive

  val to_single_nan : float -> float32

  val neg_nan : float -> float

  val abs_nan : float -> float

  val cons_pl : float -> (bool * positive) list -> (bool * positive) list

  val unop_nan : float -> float

  val binop_nan : float -> float -> float

  val fma_nan_1 : float -> float -> float -> float

  val fma_nan : float -> float -> float -> float

  val zero : float

  val eq_dec : float -> float -> bool

  val neg : float -> float

  val abs : float -> float

  val sqrt : float -> float

  val add : float -> float -> float

  val sub : float -> float -> float

  val mul : float -> float -> float

  val div : float -> float -> float

  val fma : float -> float -> float -> float

  val compare : float -> float -> Datatypes.comparison option

  val cmp : comparison -> float -> float -> bool

  val ordered : float -> float -> bool

  val of_single : float32 -> float

  val to_single : float -> float32

  val to_int : float -> Int.int option

  val to_intu : float -> Int.int option

  val to_long : float -> Int64.int option

  val to_longu : float -> Int64.int option

  val of_int : Int.int -> float

  val of_intu : Int.int -> float

  val of_long : Int64.int -> float

  val of_longu : Int64.int -> float

  val from_parsed : positive -> positive -> coq_Z -> float

  val to_bits : float -> Int64.int

  val of_bits : Int64.int -> float

  val from_words : Int.int -> Int.int -> float

  val exact_inverse : float -> float option

  val ox8000_0000 : Int.int

  val ox7FFF_FFFF : Int.int

  val ox4330_0000 : Int.int

  val ox4530_0000 : Int.int
 end

module Float32 :
 sig
  val neg_nan : float32 -> float32

  val abs_nan : float32 -> float32

  val cons_pl : float32 -> (bool * positive) list -> (bool * positive) list

  val unop_nan : float32 -> float32

  val binop_nan : float32 -> float32 -> float32

  val fma_nan_1 : float32 -> float32 -> float32 -> float32

  val fma_nan : float32 -> float32 -> float32 -> float32

  val zero : float32

  val eq_dec : float32 -> float32 -> bool

  val neg : float32 -> float32

  val abs : float32 -> float32

  val sqrt : float32 -> float32

  val add : float32 -> float32 -> float32

  val sub : float32 -> float32 -> float32

  val mul : float32 -> float32 -> float32

  val div : float32 -> float32 -> float32

  val fma : float32 -> float32 -> float32 -> float32

  val compare : float32 -> float32 -> Datatypes.comparison option

  val cmp : comparison -> float32 -> float32 -> bool

  val ordered : float32 -> float32 -> bool

  val of_double : float -> float32

  val to_double : float32 -> float

  val to_int : float32 -> Int.int option

  val to_intu : float32 -> Int.int option

  val to_long : float32 -> Int64.int option

  val to_longu : float32 -> Int64.int option

  val of_int : Int.int -> float32

  val of_intu : Int.int -> float32

  val of_long : Int64.int -> float32

  val of_longu : Int64.int -> float32

  val from_parsed : positive -> positive -> coq_Z -> float32

  val to_bits : float32 -> Int.int

  val of_bits : Int.int -> float32

  val exact_inverse : float32 -> float32 option
 end
