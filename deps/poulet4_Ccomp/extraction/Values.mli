open AST
open Archi
open BinInt
open BinNums
open Bool
open Coqlib
open Datatypes
open Floats
open Integers

type block = positive

val eq_block : positive -> positive -> bool

type coq_val =
| Vundef
| Vint of Int.int
| Vlong of Int64.int
| Vfloat of float
| Vsingle of float32
| Vptr of block * Ptrofs.int

val val_rect :
  'a1 -> (Int.int -> 'a1) -> (Int64.int -> 'a1) -> (float -> 'a1) -> (float32
  -> 'a1) -> (block -> Ptrofs.int -> 'a1) -> coq_val -> 'a1

val val_rec :
  'a1 -> (Int.int -> 'a1) -> (Int64.int -> 'a1) -> (float -> 'a1) -> (float32
  -> 'a1) -> (block -> Ptrofs.int -> 'a1) -> coq_val -> 'a1

val coq_Vzero : coq_val

val coq_Vone : coq_val

val coq_Vmone : coq_val

val coq_Vtrue : coq_val

val coq_Vfalse : coq_val

val coq_Vnullptr : coq_val

val coq_Vptrofs : Ptrofs.int -> coq_val

module Val :
 sig
  val eq : coq_val -> coq_val -> bool

  val has_type_dec : coq_val -> typ -> bool

  val neg : coq_val -> coq_val

  val negf : coq_val -> coq_val

  val absf : coq_val -> coq_val

  val negfs : coq_val -> coq_val

  val absfs : coq_val -> coq_val

  val maketotal : coq_val option -> coq_val

  val intoffloat : coq_val -> coq_val option

  val intuoffloat : coq_val -> coq_val option

  val floatofint : coq_val -> coq_val option

  val floatofintu : coq_val -> coq_val option

  val intofsingle : coq_val -> coq_val option

  val intuofsingle : coq_val -> coq_val option

  val singleofint : coq_val -> coq_val option

  val singleofintu : coq_val -> coq_val option

  val negint : coq_val -> coq_val

  val notint : coq_val -> coq_val

  val of_bool : bool -> coq_val

  val boolval : coq_val -> coq_val

  val notbool : coq_val -> coq_val

  val zero_ext : coq_Z -> coq_val -> coq_val

  val sign_ext : coq_Z -> coq_val -> coq_val

  val singleoffloat : coq_val -> coq_val

  val floatofsingle : coq_val -> coq_val

  val add : coq_val -> coq_val -> coq_val

  val sub : coq_val -> coq_val -> coq_val

  val mul : coq_val -> coq_val -> coq_val

  val mulhs : coq_val -> coq_val -> coq_val

  val mulhu : coq_val -> coq_val -> coq_val

  val divs : coq_val -> coq_val -> coq_val option

  val mods : coq_val -> coq_val -> coq_val option

  val divu : coq_val -> coq_val -> coq_val option

  val modu : coq_val -> coq_val -> coq_val option

  val add_carry : coq_val -> coq_val -> coq_val -> coq_val

  val sub_overflow : coq_val -> coq_val -> coq_val

  val negative : coq_val -> coq_val

  val coq_and : coq_val -> coq_val -> coq_val

  val coq_or : coq_val -> coq_val -> coq_val

  val xor : coq_val -> coq_val -> coq_val

  val shl : coq_val -> coq_val -> coq_val

  val shr : coq_val -> coq_val -> coq_val

  val shr_carry : coq_val -> coq_val -> coq_val

  val shrx : coq_val -> coq_val -> coq_val option

  val shru : coq_val -> coq_val -> coq_val

  val rol : coq_val -> coq_val -> coq_val

  val rolm : coq_val -> Int.int -> Int.int -> coq_val

  val ror : coq_val -> coq_val -> coq_val

  val addf : coq_val -> coq_val -> coq_val

  val subf : coq_val -> coq_val -> coq_val

  val mulf : coq_val -> coq_val -> coq_val

  val divf : coq_val -> coq_val -> coq_val

  val floatofwords : coq_val -> coq_val -> coq_val

  val addfs : coq_val -> coq_val -> coq_val

  val subfs : coq_val -> coq_val -> coq_val

  val mulfs : coq_val -> coq_val -> coq_val

  val divfs : coq_val -> coq_val -> coq_val

  val longofwords : coq_val -> coq_val -> coq_val

  val loword : coq_val -> coq_val

  val hiword : coq_val -> coq_val

  val negl : coq_val -> coq_val

  val notl : coq_val -> coq_val

  val longofint : coq_val -> coq_val

  val longofintu : coq_val -> coq_val

  val longoffloat : coq_val -> coq_val option

  val longuoffloat : coq_val -> coq_val option

  val longofsingle : coq_val -> coq_val option

  val longuofsingle : coq_val -> coq_val option

  val floatoflong : coq_val -> coq_val option

  val floatoflongu : coq_val -> coq_val option

  val singleoflong : coq_val -> coq_val option

  val singleoflongu : coq_val -> coq_val option

  val addl : coq_val -> coq_val -> coq_val

  val subl : coq_val -> coq_val -> coq_val

  val mull : coq_val -> coq_val -> coq_val

  val mull' : coq_val -> coq_val -> coq_val

  val mullhs : coq_val -> coq_val -> coq_val

  val mullhu : coq_val -> coq_val -> coq_val

  val divls : coq_val -> coq_val -> coq_val option

  val modls : coq_val -> coq_val -> coq_val option

  val divlu : coq_val -> coq_val -> coq_val option

  val modlu : coq_val -> coq_val -> coq_val option

  val addl_carry : coq_val -> coq_val -> coq_val -> coq_val

  val subl_overflow : coq_val -> coq_val -> coq_val

  val negativel : coq_val -> coq_val

  val andl : coq_val -> coq_val -> coq_val

  val orl : coq_val -> coq_val -> coq_val

  val xorl : coq_val -> coq_val -> coq_val

  val shll : coq_val -> coq_val -> coq_val

  val shrl : coq_val -> coq_val -> coq_val

  val shrlu : coq_val -> coq_val -> coq_val

  val shrxl : coq_val -> coq_val -> coq_val option

  val shrl_carry : coq_val -> coq_val -> coq_val

  val roll : coq_val -> coq_val -> coq_val

  val rorl : coq_val -> coq_val -> coq_val

  val rolml : coq_val -> Int.int -> Int64.int -> coq_val

  val zero_ext_l : coq_Z -> coq_val -> coq_val

  val sign_ext_l : coq_Z -> coq_val -> coq_val

  val cmp_bool : comparison -> coq_val -> coq_val -> bool option

  val cmp_different_blocks : comparison -> bool option

  val cmpu_bool :
    (block -> coq_Z -> bool) -> comparison -> coq_val -> coq_val -> bool
    option

  val cmpf_bool : comparison -> coq_val -> coq_val -> bool option

  val cmpfs_bool : comparison -> coq_val -> coq_val -> bool option

  val cmpl_bool : comparison -> coq_val -> coq_val -> bool option

  val cmplu_bool :
    (block -> coq_Z -> bool) -> comparison -> coq_val -> coq_val -> bool
    option

  val of_optbool : bool option -> coq_val

  val cmp : comparison -> coq_val -> coq_val -> coq_val

  val cmpu :
    (block -> coq_Z -> bool) -> comparison -> coq_val -> coq_val -> coq_val

  val cmpf : comparison -> coq_val -> coq_val -> coq_val

  val cmpfs : comparison -> coq_val -> coq_val -> coq_val

  val cmpl : comparison -> coq_val -> coq_val -> coq_val option

  val cmplu :
    (block -> coq_Z -> bool) -> comparison -> coq_val -> coq_val -> coq_val
    option

  val maskzero_bool : coq_val -> Int.int -> bool option

  val offset_ptr : coq_val -> Ptrofs.int -> coq_val

  val normalize : coq_val -> typ -> coq_val

  val select : bool option -> coq_val -> coq_val -> typ -> coq_val

  val load_result : memory_chunk -> coq_val -> coq_val

  type meminj = block -> (block * coq_Z) option
 end

val inject_id : Val.meminj

val compose_meminj : Val.meminj -> Val.meminj -> Val.meminj
