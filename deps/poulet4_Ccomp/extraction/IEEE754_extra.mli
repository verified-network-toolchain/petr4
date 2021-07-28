open BinInt
open BinNums
open BinPos
open Binary
open Datatypes
open SpecFloat
open ZArith_dec
open Zaux

val coq_Beq_dec : coq_Z -> coq_Z -> binary_float -> binary_float -> bool

val coq_BofZ : coq_Z -> coq_Z -> coq_Z -> binary_float

val coq_ZofB : coq_Z -> coq_Z -> binary_float -> coq_Z option

val coq_ZofB_range :
  coq_Z -> coq_Z -> binary_float -> coq_Z -> coq_Z -> coq_Z option

val coq_Bexact_inverse_mantissa : coq_Z -> positive

val coq_Bexact_inverse : coq_Z -> coq_Z -> binary_float -> binary_float option

val pos_pow : positive -> positive -> positive

val coq_Bparse :
  coq_Z -> coq_Z -> positive -> positive -> coq_Z -> binary_float

val coq_Bconv :
  coq_Z -> coq_Z -> coq_Z -> coq_Z -> (binary_float -> binary_float) -> mode
  -> binary_float -> binary_float
