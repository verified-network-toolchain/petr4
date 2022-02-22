From compcert Require Import Clight Ctypes Integers Cop Clightdefs.
Require Import Poulet4.Ccomp.Petr4Runtime.
Module RunTime := Petr4Runtime.
Definition long_unsigned := Tlong Unsigned noattr.
Definition long_signed := Tlong Signed noattr.
Definition int_unsigned := Tint I32 Unsigned noattr.
Definition int_signed := Tint I32 Signed noattr.
Definition char := Tint I8 Unsigned noattr.
Definition Cstring := Tpointer char noattr.
Definition Cfalse := Econst_int (Integers.Int.zero) (type_bool).
Definition Ctrue := Econst_int (Integers.Int.one) (type_bool).
Definition Cint_of_Z val:= Econst_int (Integers.Int.repr val) int_signed.
Definition Cuint_of_Z val:= Econst_int (Integers.Int.repr val) int_unsigned.
Definition Cint_one := Econst_int Integers.Int.one int_signed.
Definition Cint_zero := Econst_int Integers.Int.zero int_signed.
Definition Cuint_one := Econst_int Integers.Int.one int_unsigned.
Definition Cuint_zero := Econst_int Integers.Int.zero int_unsigned.
Definition bit_vec := 
  (Tstruct (RunTime._BitVec) noattr).
Definition table_t := 
  (Tstruct (RunTime._Table) noattr).
Definition action_ref := 
  (Tstruct (RunTime._ActionRef) noattr).
Definition TpointerBitVec := Ctypes.Tpointer bit_vec noattr.
Definition TpointerBool := Ctypes.Tpointer type_bool noattr.  
Definition TpointerTable := Ctypes.Tpointer table_t noattr.
Definition TpointerActionRef := Ctypes.Tpointer action_ref noattr.
Definition typelist_slice := 
    Ctypes.Tcons TpointerBitVec 
    (Ctypes.Tcons TpointerBitVec 
    (Ctypes.Tcons TpointerBitVec
    (Ctypes.Tcons TpointerBitVec Ctypes.Tnil))).

  Definition slice_function := 
    Evar $"eval_slice" (Tfunction typelist_slice tvoid cc_default).
  
  Definition typelist_uop := 
    Ctypes.Tcons TpointerBitVec 
    (Ctypes.Tcons TpointerBitVec Ctypes.Tnil).
  
  Definition uop_function (op: ident) := 
    Evar op (Tfunction typelist_uop tvoid cc_default).
    
  Definition typelist_bop_bitvec := 
    let TpointerBitVec := Ctypes.Tpointer bit_vec noattr in 
    Ctypes.Tcons TpointerBitVec 
    (Ctypes.Tcons TpointerBitVec
    (Ctypes.Tcons TpointerBitVec
    Ctypes.Tnil)).

  Definition typelist_bop_bool := 
    Ctypes.Tcons TpointerBitVec 
    (Ctypes.Tcons TpointerBitVec
    (Ctypes.Tcons TpointerBool
    Ctypes.Tnil)).

  Definition bop_function (op: ident) := 
    if(op == _interp_beq) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default) 
    else if(op == _interp_bne) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default) 
    else if(op == _interp_bge) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default) 
    else if(op == _interp_bgt) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default) 
    else if(op == _interp_ble) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default) 
    else if(op == _interp_blt) then
      Evar op (Tfunction typelist_bop_bool tvoid cc_default) 
    else
      Evar op (Tfunction typelist_bop_bitvec tvoid cc_default) 
    .

  Definition typelist_cast_to_bool :=   
    Ctypes.Tcons TpointerBool
    (Ctypes.Tcons bit_vec
    Ctypes.Tnil).

  Definition cast_to_bool_function := 
    Evar _init_bitvec (Tfunction typelist_cast_to_bool tvoid cc_default). 


  Definition typelist_cast_from_bool := 
    Ctypes.Tcons TpointerBitVec
    (Ctypes.Tcons type_bool
    Ctypes.Tnil).

  Definition cast_from_bool_function := 
    Evar _init_bitvec (Tfunction typelist_cast_from_bool tvoid cc_default).

  Definition typelist_cast_numbers :=
    Ctypes.Tcons TpointerBitVec 
    (Ctypes.Tcons bit_vec
    (Ctypes.Tcons int_signed
    (Ctypes.Tcons int_signed
    Ctypes.Tnil))).

  Definition cast_numbers_function := 
    Evar _init_bitvec (Tfunction typelist_cast_numbers tvoid cc_default).

  Definition typelist_bitvec_init :=
    Ctypes.Tcons TpointerBitVec 
    (Ctypes.Tcons type_bool
    (Ctypes.Tcons int_signed
    (Ctypes.Tcons Cstring
    Ctypes.Tnil))).

  Definition bitvec_init_function := 
    Evar _init_bitvec (Tfunction typelist_bitvec_init tvoid cc_default). 

  Definition typelist_table_init := 
    (Ctypes.Tcons int_signed
    (Ctypes.Tcons int_signed
    Ctypes.Tnil)).

  Definition table_init_function := 
    Evar _init_table (Tfunction typelist_table_init TpointerTable cc_default).

  Definition typelist_table_match length := 
    (Ctypes.Tcons TpointerActionRef
    (Ctypes.Tcons TpointerTable
    (Ctypes.Tcons (Tarray bit_vec length noattr)
    Ctypes.Tnil))).
  
  Definition table_match_function length := 
    Evar _table_match (Tfunction (typelist_table_match length) tvoid cc_default)
    .
