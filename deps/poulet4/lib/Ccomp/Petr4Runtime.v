From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.10".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "Petr4Runtime.c".
  Definition normalized := false.
End Info.

Definition _ActionRef : ident := $"ActionRef".
Definition _BitVec : ident := $"BitVec".
Definition _Entry : ident := $"Entry".
Definition _Pat : ident := $"Pat".
Definition _Table : ident := $"Table".
Definition __537 : ident := $"_537".
Definition ___assert_fail : ident := $"__assert_fail".
Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___func__ : ident := $"__func__".
Definition ___func____1 : ident := $"__func____1".
Definition ___gmpz_add : ident := $"__gmpz_add".
Definition ___gmpz_and : ident := $"__gmpz_and".
Definition ___gmpz_clear : ident := $"__gmpz_clear".
Definition ___gmpz_cmp : ident := $"__gmpz_cmp".
Definition ___gmpz_cmp_si : ident := $"__gmpz_cmp_si".
Definition ___gmpz_fdiv_q_2exp : ident := $"__gmpz_fdiv_q_2exp".
Definition ___gmpz_init : ident := $"__gmpz_init".
Definition ___gmpz_ior : ident := $"__gmpz_ior".
Definition ___gmpz_mod : ident := $"__gmpz_mod".
Definition ___gmpz_mul : ident := $"__gmpz_mul".
Definition ___gmpz_mul_2exp : ident := $"__gmpz_mul_2exp".
Definition ___gmpz_neg : ident := $"__gmpz_neg".
Definition ___gmpz_set : ident := $"__gmpz_set".
Definition ___gmpz_set_si : ident := $"__gmpz_set_si".
Definition ___gmpz_set_str : ident := $"__gmpz_set_str".
Definition ___gmpz_set_ui : ident := $"__gmpz_set_ui".
Definition ___gmpz_sub : ident := $"__gmpz_sub".
Definition ___gmpz_sub_ui : ident := $"__gmpz_sub_ui".
Definition ___gmpz_ui_pow_ui : ident := $"__gmpz_ui_pow_ui".
Definition ___gmpz_xor : ident := $"__gmpz_xor".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition __mp_alloc : ident := $"_mp_alloc".
Definition __mp_d : ident := $"_mp_d".
Definition __mp_size : ident := $"_mp_size".
Definition _action : ident := $"action".
Definition _actionRef : ident := $"actionRef".
Definition _action_ref : ident := $"action_ref".
Definition _add_entry : ident := $"add_entry".
Definition _arguments : ident := $"arguments".
Definition _capacity : ident := $"capacity".
Definition _check : ident := $"check".
Definition _data : ident := $"data".
Definition _default_action : ident := $"default_action".
Definition _dst : ident := $"dst".
Definition _dst_value : ident := $"dst_value".
Definition _entries : ident := $"entries".
Definition _entry : ident := $"entry".
Definition _entry_match : ident := $"entry_match".
Definition _eval_sat_add_sub : ident := $"eval_sat_add_sub".
Definition _eval_uminus : ident := $"eval_uminus".
Definition _extract_bitvec : ident := $"extract_bitvec".
Definition _extract_bool : ident := $"extract_bool".
Definition _i : ident := $"i".
Definition _in : ident := $"in".
Definition _init_action : ident := $"init_action".
Definition _init_bitvec : ident := $"init_bitvec".
Definition _init_bitvec_binary : ident := $"init_bitvec_binary".
Definition _init_entry : ident := $"init_entry".
Definition _init_pattern : ident := $"init_pattern".
Definition _init_table : ident := $"init_table".
Definition _interp_beq : ident := $"interp_beq".
Definition _interp_bge : ident := $"interp_bge".
Definition _interp_bgt : ident := $"interp_bgt".
Definition _interp_bitwise_and : ident := $"interp_bitwise_and".
Definition _interp_bitwise_or : ident := $"interp_bitwise_or".
Definition _interp_bitwise_xor : ident := $"interp_bitwise_xor".
Definition _interp_ble : ident := $"interp_ble".
Definition _interp_blt : ident := $"interp_blt".
Definition _interp_bminus : ident := $"interp_bminus".
Definition _interp_bminus_sat : ident := $"interp_bminus_sat".
Definition _interp_bmod : ident := $"interp_bmod".
Definition _interp_bmult : ident := $"interp_bmult".
Definition _interp_bne : ident := $"interp_bne".
Definition _interp_bplus : ident := $"interp_bplus".
Definition _interp_bplus_sat : ident := $"interp_bplus_sat".
Definition _interp_bshl : ident := $"interp_bshl".
Definition _interp_bshr : ident := $"interp_bshr".
Definition _interp_cast : ident := $"interp_cast".
Definition _interp_cast_from_bool : ident := $"interp_cast_from_bool".
Definition _interp_cast_to_bool : ident := $"interp_cast_to_bool".
Definition _interp_concat : ident := $"interp_concat".
Definition _interp_uminus : ident := $"interp_uminus".
Definition _is_add : ident := $"is_add".
Definition _is_signed : ident := $"is_signed".
Definition _key_masked : ident := $"key_masked".
Definition _keys : ident := $"keys".
Definition _l : ident := $"l".
Definition _left_shifted : ident := $"left_shifted".
Definition _main : ident := $"main".
Definition _malloc : ident := $"malloc".
Definition _mask : ident := $"mask".
Definition _matched : ident := $"matched".
Definition _max : ident := $"max".
Definition _min : ident := $"min".
Definition _num_args : ident := $"num_args".
Definition _num_entries : ident := $"num_entries".
Definition _num_keys : ident := $"num_keys".
Definition _packet_in : ident := $"packet_in".
Definition _pattern : ident := $"pattern".
Definition _pattern_match : ident := $"pattern_match".
Definition _pkt : ident := $"pkt".
Definition _r : ident := $"r".
Definition _reset_bitvec : ident := $"reset_bitvec".
Definition _sign : ident := $"sign".
Definition _size : ident := $"size".
Definition _src : ident := $"src".
Definition _t : ident := $"t".
Definition _table : ident := $"table".
Definition _table_match : ident := $"table_match".
Definition _top : ident := $"top".
Definition _top__1 : ident := $"top__1".
Definition _top__2 : ident := $"top__2".
Definition _v : ident := $"v".
Definition _val : ident := $"val".
Definition _val_masked : ident := $"val_masked".
Definition _value : ident := $"value".
Definition _w : ident := $"w".
Definition _width : ident := $"width".
Definition _wrap_around : ident := $"wrap_around".
Definition _x : ident := $"x".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 15);
  gvar_init := (Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_default_action := {|
  gvar_info := (Tstruct _ActionRef noattr);
  gvar_init := (Init_int32 (Int.repr 0) :: Init_space 4 ::
                Init_int64 (Int64.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_reset_bitvec := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct __537 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar ___gmpz_clear (Tfunction (Tcons (tptr (Tstruct __537 noattr)) Tnil)
                        tvoid cc_default))
  ((Etempvar _x (tptr (Tstruct __537 noattr))) :: nil))
|}.

Definition v___func__ := {|
  gvar_info := (tarray tschar 12);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_init_bitvec := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) :: (_sign, tint) ::
                (_w, tint) :: (_val, (tptr tschar)) :: nil);
  fn_vars := ((_i, (tarray (Tstruct __537 noattr) 1)) :: nil);
  fn_temps := ((_check, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar ___gmpz_init (Tfunction (Tcons (tptr (Tstruct __537 noattr)) Tnil)
                         tvoid cc_default))
    ((Evar _i (tarray (Tstruct __537 noattr) 1)) :: nil))
  (Ssequence
    (Scall None
      (Evar ___gmpz_set_ui (Tfunction
                             (Tcons (tptr (Tstruct __537 noattr))
                               (Tcons tulong Tnil)) tvoid cc_default))
      ((Evar _i (tarray (Tstruct __537 noattr) 1)) ::
       (Econst_int (Int.repr 0) tint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar ___gmpz_set_str (Tfunction
                                  (Tcons (tptr (Tstruct __537 noattr))
                                    (Tcons (tptr tschar) (Tcons tint Tnil)))
                                  tint cc_default))
          ((Evar _i (tarray (Tstruct __537 noattr) 1)) ::
           (Etempvar _val (tptr tschar)) ::
           (Econst_int (Int.repr 10) tint) :: nil))
        (Sset _check (Etempvar _t'1 tint)))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _check tint)
                       (Econst_int (Int.repr 0) tint) tint)
          Sskip
          (Scall None
            (Evar ___assert_fail (Tfunction
                                   (Tcons (tptr tschar)
                                     (Tcons (tptr tschar)
                                       (Tcons tuint
                                         (Tcons (tptr tschar) Tnil)))) tvoid
                                   cc_default))
            ((Evar ___stringlit_2 (tarray tschar 11)) ::
             (Evar ___stringlit_1 (tarray tschar 15)) ::
             (Econst_int (Int.repr 96) tint) ::
             (Evar ___func__ (tarray tschar 12)) :: nil)))
        (Ssequence
          (Scall None
            (Evar ___gmpz_init (Tfunction
                                 (Tcons (tptr (Tstruct __537 noattr)) Tnil)
                                 tvoid cc_default))
            ((Efield
               (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                 (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) :: nil))
          (Ssequence
            (Scall None
              (Evar ___gmpz_set (Tfunction
                                  (Tcons (tptr (Tstruct __537 noattr))
                                    (Tcons (tptr (Tstruct __537 noattr))
                                      Tnil)) tvoid cc_default))
              ((Efield
                 (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                   (Tstruct _BitVec noattr)) _value
                 (tarray (Tstruct __537 noattr) 1)) ::
               (Evar _i (tarray (Tstruct __537 noattr) 1)) :: nil))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                    (Tstruct _BitVec noattr)) _is_signed tint)
                (Etempvar _sign tint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                    (Tstruct _BitVec noattr)) _width tint)
                (Etempvar _w tint)))))))))
|}.

Definition v___func____1 := {|
  gvar_info := (tarray tschar 19);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_init_bitvec_binary := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) :: (_sign, tint) ::
                (_w, tint) :: (_val, (tptr tschar)) :: nil);
  fn_vars := ((_i, (tarray (Tstruct __537 noattr) 1)) :: nil);
  fn_temps := ((_check, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar ___gmpz_init (Tfunction (Tcons (tptr (Tstruct __537 noattr)) Tnil)
                         tvoid cc_default))
    ((Evar _i (tarray (Tstruct __537 noattr) 1)) :: nil))
  (Ssequence
    (Scall None
      (Evar ___gmpz_set_ui (Tfunction
                             (Tcons (tptr (Tstruct __537 noattr))
                               (Tcons tulong Tnil)) tvoid cc_default))
      ((Evar _i (tarray (Tstruct __537 noattr) 1)) ::
       (Econst_int (Int.repr 0) tint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar ___gmpz_set_str (Tfunction
                                  (Tcons (tptr (Tstruct __537 noattr))
                                    (Tcons (tptr tschar) (Tcons tint Tnil)))
                                  tint cc_default))
          ((Evar _i (tarray (Tstruct __537 noattr) 1)) ::
           (Etempvar _val (tptr tschar)) :: (Econst_int (Int.repr 2) tint) ::
           nil))
        (Sset _check (Etempvar _t'1 tint)))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _check tint)
                       (Econst_int (Int.repr 0) tint) tint)
          Sskip
          (Scall None
            (Evar ___assert_fail (Tfunction
                                   (Tcons (tptr tschar)
                                     (Tcons (tptr tschar)
                                       (Tcons tuint
                                         (Tcons (tptr tschar) Tnil)))) tvoid
                                   cc_default))
            ((Evar ___stringlit_2 (tarray tschar 11)) ::
             (Evar ___stringlit_1 (tarray tschar 15)) ::
             (Econst_int (Int.repr 118) tint) ::
             (Evar ___func____1 (tarray tschar 19)) :: nil)))
        (Ssequence
          (Scall None
            (Evar ___gmpz_init (Tfunction
                                 (Tcons (tptr (Tstruct __537 noattr)) Tnil)
                                 tvoid cc_default))
            ((Efield
               (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                 (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) :: nil))
          (Ssequence
            (Scall None
              (Evar ___gmpz_set (Tfunction
                                  (Tcons (tptr (Tstruct __537 noattr))
                                    (Tcons (tptr (Tstruct __537 noattr))
                                      Tnil)) tvoid cc_default))
              ((Efield
                 (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                   (Tstruct _BitVec noattr)) _value
                 (tarray (Tstruct __537 noattr) 1)) ::
               (Evar _i (tarray (Tstruct __537 noattr) 1)) :: nil))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                    (Tstruct _BitVec noattr)) _is_signed tint)
                (Etempvar _sign tint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                    (Tstruct _BitVec noattr)) _width tint)
                (Etempvar _w tint)))))))))
|}.

Definition f_extract_bool := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pkt, (tptr (Tstruct _packet_in noattr))) ::
                (_data, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Ederef
                   (Efield
                     (Ederef
                       (Etempvar _pkt (tptr (Tstruct _packet_in noattr)))
                       (Tstruct _packet_in noattr)) _in (tptr tuchar))
                   tuchar) (Econst_int (Int.repr 1) tint) tint)
    (Sassign (Ederef (Etempvar _data (tptr tint)) tint)
      (Econst_int (Int.repr 1) tint))
    (Sassign (Ederef (Etempvar _data (tptr tint)) tint)
      (Econst_int (Int.repr 0) tint)))
  (Sassign
    (Efield
      (Ederef (Etempvar _pkt (tptr (Tstruct _packet_in noattr)))
        (Tstruct _packet_in noattr)) _in (tptr tuchar))
    (Ebinop Oadd
      (Efield
        (Ederef (Etempvar _pkt (tptr (Tstruct _packet_in noattr)))
          (Tstruct _packet_in noattr)) _in (tptr tuchar))
      (Econst_int (Int.repr 1) tint) (tptr tuchar))))
|}.

Definition f_extract_bitvec := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pkt, (tptr (Tstruct _packet_in noattr))) ::
                (_data, (tptr (Tstruct _BitVec noattr))) ::
                (_is_signed, tint) :: (_width, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_val, (tptr tschar)) :: (_i, tint) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Ebinop Omul (Esizeof tschar tulong) (Etempvar _width tint) tulong) ::
       nil))
    (Sset _val (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tschar))))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _width tint)
                         tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _val (tptr tschar)) (Etempvar _i tint)
                  (tptr tschar)) tschar)
              (Ebinop Oadd
                (Ederef
                  (Efield
                    (Ederef
                      (Etempvar _pkt (tptr (Tstruct _packet_in noattr)))
                      (Tstruct _packet_in noattr)) _in (tptr tuchar)) tuchar)
                (Econst_int (Int.repr 48) tint) tint))
            (Sassign
              (Efield
                (Ederef (Etempvar _pkt (tptr (Tstruct _packet_in noattr)))
                  (Tstruct _packet_in noattr)) _in (tptr tuchar))
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _pkt (tptr (Tstruct _packet_in noattr)))
                    (Tstruct _packet_in noattr)) _in (tptr tuchar))
                (Econst_int (Int.repr 1) tint) (tptr tuchar)))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Scall None
      (Evar _init_bitvec_binary (Tfunction
                                  (Tcons (tptr (Tstruct _BitVec noattr))
                                    (Tcons tint
                                      (Tcons tint (Tcons (tptr tschar) Tnil))))
                                  tvoid cc_default))
      ((Etempvar _data (tptr (Tstruct _BitVec noattr))) ::
       (Etempvar _is_signed tint) :: (Etempvar _width tint) ::
       (Etempvar _val (tptr tschar)) :: nil))))
|}.

Definition f_eval_uminus := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct __537 noattr))) :: nil);
  fn_vars := ((_dst_value, (tarray (Tstruct __537 noattr) 1)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar ___gmpz_init (Tfunction (Tcons (tptr (Tstruct __537 noattr)) Tnil)
                         tvoid cc_default))
    ((Evar _dst_value (tarray (Tstruct __537 noattr) 1)) :: nil))
  (Ssequence
    (Scall None
      (Evar ___gmpz_set_ui (Tfunction
                             (Tcons (tptr (Tstruct __537 noattr))
                               (Tcons tulong Tnil)) tvoid cc_default))
      ((Evar _dst_value (tarray (Tstruct __537 noattr) 1)) ::
       (Econst_int (Int.repr 0) tint) :: nil))
    (Scall None
      (Evar ___gmpz_neg (Tfunction
                          (Tcons (tptr (Tstruct __537 noattr))
                            (Tcons (tptr (Tstruct __537 noattr)) Tnil)) tvoid
                          cc_default))
      ((Evar _dst_value (tarray (Tstruct __537 noattr) 1)) ::
       (Etempvar _v (tptr (Tstruct __537 noattr))) :: nil))))
|}.

Definition f_interp_uminus := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_src, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_src, (Tstruct _BitVec noattr)) ::
              (_top, (tarray (Tstruct __537 noattr) 1)) ::
              (_top__1, (tarray (Tstruct __537 noattr) 1)) :: nil);
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _src (Tstruct _BitVec noattr))
    (Etempvar _src (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
          (Tstruct _BitVec noattr)) _width tint)
      (Efield (Evar _src (Tstruct _BitVec noattr)) _width tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
            (Tstruct _BitVec noattr)) _is_signed tint)
        (Efield (Evar _src (Tstruct _BitVec noattr)) _is_signed tint))
      (Ssequence
        (Scall None
          (Evar ___gmpz_init (Tfunction
                               (Tcons (tptr (Tstruct __537 noattr)) Tnil)
                               tvoid cc_default))
          ((Efield
             (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
               (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __537 noattr) 1)) :: nil))
        (Sifthenelse (Efield (Evar _src (Tstruct _BitVec noattr)) _is_signed
                       tint)
          (Ssequence
            (Scall None
              (Evar ___gmpz_neg (Tfunction
                                  (Tcons (tptr (Tstruct __537 noattr))
                                    (Tcons (tptr (Tstruct __537 noattr))
                                      Tnil)) tvoid cc_default))
              ((Efield
                 (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                   (Tstruct _BitVec noattr)) _value
                 (tarray (Tstruct __537 noattr) 1)) ::
               (Efield (Evar _src (Tstruct _BitVec noattr)) _value
                 (tarray (Tstruct __537 noattr) 1)) :: nil))
            (Ssequence
              (Scall None
                (Evar ___gmpz_init (Tfunction
                                     (Tcons (tptr (Tstruct __537 noattr))
                                       Tnil) tvoid cc_default))
                ((Evar _top (tarray (Tstruct __537 noattr) 1)) :: nil))
              (Ssequence
                (Scall None
                  (Evar ___gmpz_ui_pow_ui (Tfunction
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              (Tcons tulong
                                                (Tcons tulong Tnil))) tvoid
                                            cc_default))
                  ((Evar _top (tarray (Tstruct __537 noattr) 1)) ::
                   (Econst_int (Int.repr 2) tint) ::
                   (Ebinop Osub
                     (Efield (Evar _src (Tstruct _BitVec noattr)) _width
                       tint) (Econst_int (Int.repr 1) tint) tint) :: nil))
                (Ssequence
                  (Scall (Some _t'1)
                    (Evar ___gmpz_cmp (Tfunction
                                        (Tcons (tptr (Tstruct __537 noattr))
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            Tnil)) tint cc_default))
                    ((Efield
                       (Ederef
                         (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                         (Tstruct _BitVec noattr)) _value
                       (tarray (Tstruct __537 noattr) 1)) ::
                     (Evar _top (tarray (Tstruct __537 noattr) 1)) :: nil))
                  (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                                 (Econst_int (Int.repr 0) tint) tint)
                    (Scall None
                      (Evar ___gmpz_set (Tfunction
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              Tnil)) tvoid cc_default))
                      ((Efield
                         (Ederef
                           (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                           (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Efield (Evar _src (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) :: nil))
                    Sskip)))))
          (Ssequence
            (Scall None
              (Evar ___gmpz_init (Tfunction
                                   (Tcons (tptr (Tstruct __537 noattr)) Tnil)
                                   tvoid cc_default))
              ((Evar _top__1 (tarray (Tstruct __537 noattr) 1)) :: nil))
            (Ssequence
              (Scall None
                (Evar ___gmpz_ui_pow_ui (Tfunction
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons tulong
                                              (Tcons tulong Tnil))) tvoid
                                          cc_default))
                ((Evar _top__1 (tarray (Tstruct __537 noattr) 1)) ::
                 (Econst_int (Int.repr 2) tint) ::
                 (Efield (Evar _src (Tstruct _BitVec noattr)) _width tint) ::
                 nil))
              (Scall None
                (Evar ___gmpz_sub (Tfunction
                                    (Tcons (tptr (Tstruct __537 noattr))
                                      (Tcons (tptr (Tstruct __537 noattr))
                                        (Tcons (tptr (Tstruct __537 noattr))
                                          Tnil))) tvoid cc_default))
                ((Efield
                   (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                     (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __537 noattr) 1)) ::
                 (Evar _top__1 (tarray (Tstruct __537 noattr) 1)) ::
                 (Efield (Evar _src (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __537 noattr) 1)) :: nil)))))))))
|}.

Definition f_eval_sat_add_sub := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: (_is_add, tint) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_min, (tarray (Tstruct __537 noattr) 1)) ::
              (_max, (tarray (Tstruct __537 noattr) 1)) :: nil);
  fn_temps := ((_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Scall None
        (Evar ___gmpz_init (Tfunction
                             (Tcons (tptr (Tstruct __537 noattr)) Tnil) tvoid
                             cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) :: nil))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) _width tint)
          (Efield (Evar _l (Tstruct _BitVec noattr)) _width tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                (Tstruct _BitVec noattr)) _is_signed tint)
            (Efield (Evar _l (Tstruct _BitVec noattr)) _is_signed tint))
          (Ssequence
            (Scall None
              (Evar ___gmpz_init (Tfunction
                                   (Tcons (tptr (Tstruct __537 noattr)) Tnil)
                                   tvoid cc_default))
              ((Evar _min (tarray (Tstruct __537 noattr) 1)) :: nil))
            (Ssequence
              (Scall None
                (Evar ___gmpz_init (Tfunction
                                     (Tcons (tptr (Tstruct __537 noattr))
                                       Tnil) tvoid cc_default))
                ((Evar _max (tarray (Tstruct __537 noattr) 1)) :: nil))
              (Ssequence
                (Ssequence
                  (Sifthenelse (Ebinop Oeq
                                 (Efield (Evar _l (Tstruct _BitVec noattr))
                                   _is_signed tint)
                                 (Econst_int (Int.repr 1) tint) tint)
                    (Sset _t'1
                      (Ecast
                        (Ebinop Oeq
                          (Efield (Evar _r (Tstruct _BitVec noattr))
                            _is_signed tint) (Econst_int (Int.repr 1) tint)
                          tint) tbool))
                    (Sset _t'1 (Econst_int (Int.repr 0) tint)))
                  (Sifthenelse (Etempvar _t'1 tint)
                    (Ssequence
                      (Scall None
                        (Evar ___gmpz_ui_pow_ui (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct __537 noattr))
                                                    (Tcons tulong
                                                      (Tcons tulong Tnil)))
                                                  tvoid cc_default))
                        ((Evar _min (tarray (Tstruct __537 noattr) 1)) ::
                         (Econst_int (Int.repr 2) tint) ::
                         (Ebinop Osub
                           (Efield (Evar _l (Tstruct _BitVec noattr)) _width
                             tint) (Econst_int (Int.repr 1) tint) tint) ::
                         nil))
                      (Ssequence
                        (Scall None
                          (Evar ___gmpz_neg (Tfunction
                                              (Tcons
                                                (tptr (Tstruct __537 noattr))
                                                (Tcons
                                                  (tptr (Tstruct __537 noattr))
                                                  Tnil)) tvoid cc_default))
                          ((Evar _min (tarray (Tstruct __537 noattr) 1)) ::
                           (Evar _min (tarray (Tstruct __537 noattr) 1)) ::
                           nil))
                        (Ssequence
                          (Scall None
                            (Evar ___gmpz_ui_pow_ui (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct __537 noattr))
                                                        (Tcons tulong
                                                          (Tcons tulong Tnil)))
                                                      tvoid cc_default))
                            ((Evar _max (tarray (Tstruct __537 noattr) 1)) ::
                             (Econst_int (Int.repr 2) tint) ::
                             (Ebinop Osub
                               (Efield (Evar _l (Tstruct _BitVec noattr))
                                 _width tint) (Econst_int (Int.repr 1) tint)
                               tint) :: nil))
                          (Scall None
                            (Evar ___gmpz_sub_ui (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct __537 noattr))
                                                     (Tcons
                                                       (tptr (Tstruct __537 noattr))
                                                       (Tcons tulong Tnil)))
                                                   tvoid cc_default))
                            ((Evar _max (tarray (Tstruct __537 noattr) 1)) ::
                             (Evar _max (tarray (Tstruct __537 noattr) 1)) ::
                             (Econst_int (Int.repr 1) tint) :: nil)))))
                    (Ssequence
                      (Scall None
                        (Evar ___gmpz_set_ui (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct __537 noattr))
                                                 (Tcons tulong Tnil)) tvoid
                                               cc_default))
                        ((Evar _min (tarray (Tstruct __537 noattr) 1)) ::
                         (Econst_int (Int.repr 0) tint) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar ___gmpz_neg (Tfunction
                                              (Tcons
                                                (tptr (Tstruct __537 noattr))
                                                (Tcons
                                                  (tptr (Tstruct __537 noattr))
                                                  Tnil)) tvoid cc_default))
                          ((Evar _min (tarray (Tstruct __537 noattr) 1)) ::
                           (Evar _min (tarray (Tstruct __537 noattr) 1)) ::
                           nil))
                        (Ssequence
                          (Scall None
                            (Evar ___gmpz_ui_pow_ui (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct __537 noattr))
                                                        (Tcons tulong
                                                          (Tcons tulong Tnil)))
                                                      tvoid cc_default))
                            ((Evar _max (tarray (Tstruct __537 noattr) 1)) ::
                             (Econst_int (Int.repr 2) tint) ::
                             (Efield (Evar _l (Tstruct _BitVec noattr))
                               _width tint) :: nil))
                          (Scall None
                            (Evar ___gmpz_sub_ui (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct __537 noattr))
                                                     (Tcons
                                                       (tptr (Tstruct __537 noattr))
                                                       (Tcons tulong Tnil)))
                                                   tvoid cc_default))
                            ((Evar _max (tarray (Tstruct __537 noattr) 1)) ::
                             (Evar _max (tarray (Tstruct __537 noattr) 1)) ::
                             (Econst_int (Int.repr 1) tint) :: nil)))))))
                (Ssequence
                  (Scall None
                    (Evar ___gmpz_mul (Tfunction
                                        (Tcons (tptr (Tstruct __537 noattr))
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              Tnil))) tvoid cc_default))
                    ((Efield (Evar _r (Tstruct _BitVec noattr)) _value
                       (tarray (Tstruct __537 noattr) 1)) ::
                     (Efield (Evar _r (Tstruct _BitVec noattr)) _value
                       (tarray (Tstruct __537 noattr) 1)) ::
                     (Etempvar _is_add tint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar ___gmpz_add (Tfunction
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              (Tcons
                                                (tptr (Tstruct __537 noattr))
                                                Tnil))) tvoid cc_default))
                      ((Efield
                         (Ederef
                           (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                           (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Efield (Evar _l (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Efield (Evar _r (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) :: nil))
                    (Ssequence
                      (Scall (Some _t'3)
                        (Evar ___gmpz_cmp (Tfunction
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              (Tcons
                                                (tptr (Tstruct __537 noattr))
                                                Tnil)) tint cc_default))
                        ((Efield
                           (Ederef
                             (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                             (Tstruct _BitVec noattr)) _value
                           (tarray (Tstruct __537 noattr) 1)) ::
                         (Evar _min (tarray (Tstruct __537 noattr) 1)) ::
                         nil))
                      (Sifthenelse (Ebinop Olt (Etempvar _t'3 tint)
                                     (Econst_int (Int.repr 0) tint) tint)
                        (Scall None
                          (Evar ___gmpz_set (Tfunction
                                              (Tcons
                                                (tptr (Tstruct __537 noattr))
                                                (Tcons
                                                  (tptr (Tstruct __537 noattr))
                                                  Tnil)) tvoid cc_default))
                          ((Efield
                             (Ederef
                               (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                               (Tstruct _BitVec noattr)) _value
                             (tarray (Tstruct __537 noattr) 1)) ::
                           (Evar _min (tarray (Tstruct __537 noattr) 1)) ::
                           nil))
                        (Ssequence
                          (Scall (Some _t'2)
                            (Evar ___gmpz_cmp (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct __537 noattr))
                                                  (Tcons
                                                    (tptr (Tstruct __537 noattr))
                                                    Tnil)) tint cc_default))
                            ((Efield
                               (Ederef
                                 (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                                 (Tstruct _BitVec noattr)) _value
                               (tarray (Tstruct __537 noattr) 1)) ::
                             (Evar _max (tarray (Tstruct __537 noattr) 1)) ::
                             nil))
                          (Sifthenelse (Ebinop Ogt (Etempvar _t'2 tint)
                                         (Econst_int (Int.repr 0) tint) tint)
                            (Scall None
                              (Evar ___gmpz_set (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct __537 noattr))
                                                    (Tcons
                                                      (tptr (Tstruct __537 noattr))
                                                      Tnil)) tvoid
                                                  cc_default))
                              ((Efield
                                 (Ederef
                                   (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                                   (Tstruct _BitVec noattr)) _value
                                 (tarray (Tstruct __537 noattr) 1)) ::
                               (Evar _max (tarray (Tstruct __537 noattr) 1)) ::
                               nil))
                            Sskip))))))))))))))
|}.

Definition f_wrap_around := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) :: nil);
  fn_vars := ((_min, (tarray (Tstruct __537 noattr) 1)) ::
              (_max, (tarray (Tstruct __537 noattr) 1)) :: nil);
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar ___gmpz_init (Tfunction (Tcons (tptr (Tstruct __537 noattr)) Tnil)
                         tvoid cc_default))
    ((Evar _min (tarray (Tstruct __537 noattr) 1)) :: nil))
  (Ssequence
    (Scall None
      (Evar ___gmpz_init (Tfunction
                           (Tcons (tptr (Tstruct __537 noattr)) Tnil) tvoid
                           cc_default))
      ((Evar _max (tarray (Tstruct __537 noattr) 1)) :: nil))
    (Ssequence
      (Scall None
        (Evar ___gmpz_ui_pow_ui (Tfunction
                                  (Tcons (tptr (Tstruct __537 noattr))
                                    (Tcons tulong (Tcons tulong Tnil))) tvoid
                                  cc_default))
        ((Evar _min (tarray (Tstruct __537 noattr) 1)) ::
         (Econst_int (Int.repr 2) tint) ::
         (Ebinop Osub
           (Efield
             (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
               (Tstruct _BitVec noattr)) _width tint)
           (Econst_int (Int.repr 1) tint) tint) :: nil))
      (Ssequence
        (Scall None
          (Evar ___gmpz_neg (Tfunction
                              (Tcons (tptr (Tstruct __537 noattr))
                                (Tcons (tptr (Tstruct __537 noattr)) Tnil))
                              tvoid cc_default))
          ((Evar _min (tarray (Tstruct __537 noattr) 1)) ::
           (Evar _min (tarray (Tstruct __537 noattr) 1)) :: nil))
        (Ssequence
          (Scall None
            (Evar ___gmpz_ui_pow_ui (Tfunction
                                      (Tcons (tptr (Tstruct __537 noattr))
                                        (Tcons tulong (Tcons tulong Tnil)))
                                      tvoid cc_default))
            ((Evar _max (tarray (Tstruct __537 noattr) 1)) ::
             (Econst_int (Int.repr 2) tint) ::
             (Ebinop Osub
               (Efield
                 (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                   (Tstruct _BitVec noattr)) _width tint)
               (Econst_int (Int.repr 1) tint) tint) :: nil))
          (Ssequence
            (Scall None
              (Evar ___gmpz_sub_ui (Tfunction
                                     (Tcons (tptr (Tstruct __537 noattr))
                                       (Tcons (tptr (Tstruct __537 noattr))
                                         (Tcons tulong Tnil))) tvoid
                                     cc_default))
              ((Evar _max (tarray (Tstruct __537 noattr) 1)) ::
               (Evar _max (tarray (Tstruct __537 noattr) 1)) ::
               (Econst_int (Int.repr 1) tint) :: nil))
            (Ssequence
              (Ssequence
                (Scall (Some _t'1)
                  (Evar ___gmpz_cmp (Tfunction
                                      (Tcons (tptr (Tstruct __537 noattr))
                                        (Tcons (tptr (Tstruct __537 noattr))
                                          Tnil)) tint cc_default))
                  ((Efield
                     (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                       (Tstruct _BitVec noattr)) _value
                     (tarray (Tstruct __537 noattr) 1)) ::
                   (Evar _max (tarray (Tstruct __537 noattr) 1)) :: nil))
                (Sifthenelse (Ebinop Ogt (Etempvar _t'1 tint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Ssequence
                    (Scall None
                      (Evar ___gmpz_sub (Tfunction
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              (Tcons
                                                (tptr (Tstruct __537 noattr))
                                                Tnil))) tvoid cc_default))
                      ((Efield
                         (Ederef
                           (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                           (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Efield
                         (Ederef
                           (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                           (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Evar _max (tarray (Tstruct __537 noattr) 1)) :: nil))
                    (Scall None
                      (Evar ___gmpz_add (Tfunction
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              (Tcons
                                                (tptr (Tstruct __537 noattr))
                                                Tnil))) tvoid cc_default))
                      ((Efield
                         (Ederef
                           (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                           (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Efield
                         (Ederef
                           (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                           (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Evar _min (tarray (Tstruct __537 noattr) 1)) :: nil)))
                  Sskip))
              (Ssequence
                (Scall (Some _t'2)
                  (Evar ___gmpz_cmp (Tfunction
                                      (Tcons (tptr (Tstruct __537 noattr))
                                        (Tcons (tptr (Tstruct __537 noattr))
                                          Tnil)) tint cc_default))
                  ((Efield
                     (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                       (Tstruct _BitVec noattr)) _value
                     (tarray (Tstruct __537 noattr) 1)) ::
                   (Evar _min (tarray (Tstruct __537 noattr) 1)) :: nil))
                (Sifthenelse (Ebinop Olt (Etempvar _t'2 tint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Ssequence
                    (Scall None
                      (Evar ___gmpz_sub (Tfunction
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              (Tcons
                                                (tptr (Tstruct __537 noattr))
                                                Tnil))) tvoid cc_default))
                      ((Efield
                         (Ederef
                           (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                           (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Efield
                         (Ederef
                           (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                           (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Evar _min (tarray (Tstruct __537 noattr) 1)) :: nil))
                    (Scall None
                      (Evar ___gmpz_add (Tfunction
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              (Tcons
                                                (tptr (Tstruct __537 noattr))
                                                Tnil))) tvoid cc_default))
                      ((Efield
                         (Ederef
                           (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                           (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Efield
                         (Ederef
                           (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                           (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Evar _max (tarray (Tstruct __537 noattr) 1)) :: nil)))
                  Sskip)))))))))
|}.

Definition f_interp_bplus := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_top, (tarray (Tstruct __537 noattr) 1)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Scall None
        (Evar ___gmpz_init (Tfunction
                             (Tcons (tptr (Tstruct __537 noattr)) Tnil) tvoid
                             cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) :: nil))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) _width tint)
          (Efield (Evar _l (Tstruct _BitVec noattr)) _width tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                (Tstruct _BitVec noattr)) _is_signed tint)
            (Efield (Evar _l (Tstruct _BitVec noattr)) _is_signed tint))
          (Sifthenelse (Efield (Evar _l (Tstruct _BitVec noattr)) _is_signed
                         tint)
            (Ssequence
              (Scall None
                (Evar ___gmpz_add (Tfunction
                                    (Tcons (tptr (Tstruct __537 noattr))
                                      (Tcons (tptr (Tstruct __537 noattr))
                                        (Tcons (tptr (Tstruct __537 noattr))
                                          Tnil))) tvoid cc_default))
                ((Efield
                   (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                     (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __537 noattr) 1)) ::
                 (Efield (Evar _l (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __537 noattr) 1)) ::
                 (Efield (Evar _r (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __537 noattr) 1)) :: nil))
              (Scall None
                (Evar _wrap_around (Tfunction
                                     (Tcons (tptr (Tstruct _BitVec noattr))
                                       Tnil) tvoid cc_default))
                ((Etempvar _dst (tptr (Tstruct _BitVec noattr))) :: nil)))
            (Ssequence
              (Scall None
                (Evar ___gmpz_init (Tfunction
                                     (Tcons (tptr (Tstruct __537 noattr))
                                       Tnil) tvoid cc_default))
                ((Evar _top (tarray (Tstruct __537 noattr) 1)) :: nil))
              (Ssequence
                (Scall None
                  (Evar ___gmpz_ui_pow_ui (Tfunction
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              (Tcons tulong
                                                (Tcons tulong Tnil))) tvoid
                                            cc_default))
                  ((Evar _top (tarray (Tstruct __537 noattr) 1)) ::
                   (Econst_int (Int.repr 2) tint) ::
                   (Efield
                     (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                       (Tstruct _BitVec noattr)) _width tint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar ___gmpz_add (Tfunction
                                        (Tcons (tptr (Tstruct __537 noattr))
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              Tnil))) tvoid cc_default))
                    ((Efield
                       (Ederef
                         (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                         (Tstruct _BitVec noattr)) _value
                       (tarray (Tstruct __537 noattr) 1)) ::
                     (Efield (Evar _l (Tstruct _BitVec noattr)) _value
                       (tarray (Tstruct __537 noattr) 1)) ::
                     (Efield (Evar _r (Tstruct _BitVec noattr)) _value
                       (tarray (Tstruct __537 noattr) 1)) :: nil))
                  (Scall None
                    (Evar ___gmpz_mod (Tfunction
                                        (Tcons (tptr (Tstruct __537 noattr))
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              Tnil))) tvoid cc_default))
                    ((Efield
                       (Ederef
                         (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                         (Tstruct _BitVec noattr)) _value
                       (tarray (Tstruct __537 noattr) 1)) ::
                     (Efield
                       (Ederef
                         (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                         (Tstruct _BitVec noattr)) _value
                       (tarray (Tstruct __537 noattr) 1)) ::
                     (Evar _top (tarray (Tstruct __537 noattr) 1)) :: nil)))))))))))
|}.

Definition f_interp_bplus_sat := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Scall None
      (Evar _eval_sat_add_sub (Tfunction
                                (Tcons (tptr (Tstruct _BitVec noattr))
                                  (Tcons (Tstruct _BitVec noattr)
                                    (Tcons (Tstruct _BitVec noattr)
                                      (Tcons tint Tnil)))) tvoid cc_default))
      ((Etempvar _dst (tptr (Tstruct _BitVec noattr))) ::
       (Evar _l (Tstruct _BitVec noattr)) ::
       (Evar _r (Tstruct _BitVec noattr)) ::
       (Econst_int (Int.repr 1) tint) :: nil))))
|}.

Definition f_interp_bminus := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_top, (tarray (Tstruct __537 noattr) 1)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Scall None
        (Evar ___gmpz_init (Tfunction
                             (Tcons (tptr (Tstruct __537 noattr)) Tnil) tvoid
                             cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) :: nil))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) _width tint)
          (Efield (Evar _l (Tstruct _BitVec noattr)) _width tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                (Tstruct _BitVec noattr)) _is_signed tint)
            (Efield (Evar _l (Tstruct _BitVec noattr)) _is_signed tint))
          (Sifthenelse (Efield (Evar _l (Tstruct _BitVec noattr)) _is_signed
                         tint)
            (Ssequence
              (Scall None
                (Evar ___gmpz_sub (Tfunction
                                    (Tcons (tptr (Tstruct __537 noattr))
                                      (Tcons (tptr (Tstruct __537 noattr))
                                        (Tcons (tptr (Tstruct __537 noattr))
                                          Tnil))) tvoid cc_default))
                ((Efield
                   (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                     (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __537 noattr) 1)) ::
                 (Efield (Evar _l (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __537 noattr) 1)) ::
                 (Efield (Evar _r (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __537 noattr) 1)) :: nil))
              (Scall None
                (Evar _wrap_around (Tfunction
                                     (Tcons (tptr (Tstruct _BitVec noattr))
                                       Tnil) tvoid cc_default))
                ((Etempvar _dst (tptr (Tstruct _BitVec noattr))) :: nil)))
            (Ssequence
              (Scall None
                (Evar ___gmpz_init (Tfunction
                                     (Tcons (tptr (Tstruct __537 noattr))
                                       Tnil) tvoid cc_default))
                ((Evar _top (tarray (Tstruct __537 noattr) 1)) :: nil))
              (Ssequence
                (Scall None
                  (Evar ___gmpz_ui_pow_ui (Tfunction
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              (Tcons tulong
                                                (Tcons tulong Tnil))) tvoid
                                            cc_default))
                  ((Evar _top (tarray (Tstruct __537 noattr) 1)) ::
                   (Econst_int (Int.repr 2) tint) ::
                   (Efield (Evar _r (Tstruct _BitVec noattr)) _width tint) ::
                   nil))
                (Ssequence
                  (Scall None
                    (Evar ___gmpz_sub (Tfunction
                                        (Tcons (tptr (Tstruct __537 noattr))
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              Tnil))) tvoid cc_default))
                    ((Efield
                       (Ederef
                         (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                         (Tstruct _BitVec noattr)) _value
                       (tarray (Tstruct __537 noattr) 1)) ::
                     (Evar _top (tarray (Tstruct __537 noattr) 1)) ::
                     (Efield (Evar _r (Tstruct _BitVec noattr)) _value
                       (tarray (Tstruct __537 noattr) 1)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar ___gmpz_add (Tfunction
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              (Tcons
                                                (tptr (Tstruct __537 noattr))
                                                Tnil))) tvoid cc_default))
                      ((Efield
                         (Ederef
                           (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                           (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Efield
                         (Ederef
                           (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                           (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Efield (Evar _l (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) :: nil))
                    (Scall None
                      (Evar ___gmpz_mod (Tfunction
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              (Tcons
                                                (tptr (Tstruct __537 noattr))
                                                Tnil))) tvoid cc_default))
                      ((Efield
                         (Ederef
                           (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                           (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Efield
                         (Ederef
                           (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                           (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Evar _top (tarray (Tstruct __537 noattr) 1)) :: nil))))))))))))
|}.

Definition f_interp_bminus_sat := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Scall None
      (Evar _eval_sat_add_sub (Tfunction
                                (Tcons (tptr (Tstruct _BitVec noattr))
                                  (Tcons (Tstruct _BitVec noattr)
                                    (Tcons (Tstruct _BitVec noattr)
                                      (Tcons tint Tnil)))) tvoid cc_default))
      ((Etempvar _dst (tptr (Tstruct _BitVec noattr))) ::
       (Evar _l (Tstruct _BitVec noattr)) ::
       (Evar _r (Tstruct _BitVec noattr)) ::
       (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) :: nil))))
|}.

Definition f_interp_bmult := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_top, (tarray (Tstruct __537 noattr) 1)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Scall None
        (Evar ___gmpz_init (Tfunction
                             (Tcons (tptr (Tstruct __537 noattr)) Tnil) tvoid
                             cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) :: nil))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) _width tint)
          (Efield (Evar _l (Tstruct _BitVec noattr)) _width tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                (Tstruct _BitVec noattr)) _is_signed tint)
            (Efield (Evar _l (Tstruct _BitVec noattr)) _is_signed tint))
          (Ssequence
            (Scall None
              (Evar ___gmpz_mul (Tfunction
                                  (Tcons (tptr (Tstruct __537 noattr))
                                    (Tcons (tptr (Tstruct __537 noattr))
                                      (Tcons (tptr (Tstruct __537 noattr))
                                        Tnil))) tvoid cc_default))
              ((Efield
                 (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                   (Tstruct _BitVec noattr)) _value
                 (tarray (Tstruct __537 noattr) 1)) ::
               (Efield (Evar _l (Tstruct _BitVec noattr)) _value
                 (tarray (Tstruct __537 noattr) 1)) ::
               (Efield (Evar _r (Tstruct _BitVec noattr)) _value
                 (tarray (Tstruct __537 noattr) 1)) :: nil))
            (Ssequence
              (Scall None
                (Evar ___gmpz_init (Tfunction
                                     (Tcons (tptr (Tstruct __537 noattr))
                                       Tnil) tvoid cc_default))
                ((Evar _top (tarray (Tstruct __537 noattr) 1)) :: nil))
              (Ssequence
                (Scall None
                  (Evar ___gmpz_ui_pow_ui (Tfunction
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              (Tcons tulong
                                                (Tcons tulong Tnil))) tvoid
                                            cc_default))
                  ((Evar _top (tarray (Tstruct __537 noattr) 1)) ::
                   (Econst_int (Int.repr 2) tint) ::
                   (Efield (Evar _l (Tstruct _BitVec noattr)) _width tint) ::
                   nil))
                (Ssequence
                  (Scall None
                    (Evar ___gmpz_mod (Tfunction
                                        (Tcons (tptr (Tstruct __537 noattr))
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              Tnil))) tvoid cc_default))
                    ((Efield
                       (Ederef
                         (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                         (Tstruct _BitVec noattr)) _value
                       (tarray (Tstruct __537 noattr) 1)) ::
                     (Efield
                       (Ederef
                         (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                         (Tstruct _BitVec noattr)) _value
                       (tarray (Tstruct __537 noattr) 1)) ::
                     (Evar _top (tarray (Tstruct __537 noattr) 1)) :: nil))
                  (Sifthenelse (Efield
                                 (Ederef
                                   (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                                   (Tstruct _BitVec noattr)) _is_signed tint)
                    (Scall None
                      (Evar _wrap_around (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _BitVec noattr))
                                             Tnil) tvoid cc_default))
                      ((Etempvar _dst (tptr (Tstruct _BitVec noattr))) ::
                       nil))
                    Sskip))))))))))
|}.

Definition f_interp_bmod := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Scall None
        (Evar ___gmpz_init (Tfunction
                             (Tcons (tptr (Tstruct __537 noattr)) Tnil) tvoid
                             cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) :: nil))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) _width tint)
          (Efield (Evar _l (Tstruct _BitVec noattr)) _width tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                (Tstruct _BitVec noattr)) _is_signed tint)
            (Efield (Evar _l (Tstruct _BitVec noattr)) _is_signed tint))
          (Scall None
            (Evar ___gmpz_mod (Tfunction
                                (Tcons (tptr (Tstruct __537 noattr))
                                  (Tcons (tptr (Tstruct __537 noattr))
                                    (Tcons (tptr (Tstruct __537 noattr))
                                      Tnil))) tvoid cc_default))
            ((Efield
               (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                 (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) ::
             (Efield (Evar _l (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) ::
             (Efield (Evar _r (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) :: nil)))))))
|}.

Definition f_interp_bshl := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Scall None
        (Evar ___gmpz_init (Tfunction
                             (Tcons (tptr (Tstruct __537 noattr)) Tnil) tvoid
                             cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) :: nil))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) _width tint)
          (Efield (Evar _l (Tstruct _BitVec noattr)) _width tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                (Tstruct _BitVec noattr)) _is_signed tint)
            (Efield (Evar _l (Tstruct _BitVec noattr)) _is_signed tint))
          (Scall None
            (Evar ___gmpz_mul_2exp (Tfunction
                                     (Tcons (tptr (Tstruct __537 noattr))
                                       (Tcons (tptr (Tstruct __537 noattr))
                                         (Tcons tulong Tnil))) tvoid
                                     cc_default))
            ((Efield
               (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                 (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) ::
             (Efield (Evar _l (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) ::
             (Efield (Evar _r (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) :: nil)))))))
|}.

Definition f_interp_bshr := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Scall None
        (Evar ___gmpz_init (Tfunction
                             (Tcons (tptr (Tstruct __537 noattr)) Tnil) tvoid
                             cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) :: nil))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) _width tint)
          (Efield (Evar _l (Tstruct _BitVec noattr)) _width tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                (Tstruct _BitVec noattr)) _is_signed tint)
            (Efield (Evar _l (Tstruct _BitVec noattr)) _is_signed tint))
          (Scall None
            (Evar ___gmpz_fdiv_q_2exp (Tfunction
                                        (Tcons (tptr (Tstruct __537 noattr))
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons tulong Tnil))) tvoid
                                        cc_default))
            ((Efield
               (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                 (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) ::
             (Efield (Evar _l (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) ::
             (Efield (Evar _r (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) :: nil)))))))
|}.

Definition f_interp_ble := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr tint)) :: (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Scall (Some _t'1)
        (Evar ___gmpz_cmp (Tfunction
                            (Tcons (tptr (Tstruct __537 noattr))
                              (Tcons (tptr (Tstruct __537 noattr)) Tnil))
                            tint cc_default))
        ((Efield (Evar _l (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) ::
         (Efield (Evar _r (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) :: nil))
      (Sifthenelse (Ebinop Ole (Etempvar _t'1 tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
          (Econst_int (Int.repr 1) tint))
        (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
          (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_interp_bge := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr tint)) :: (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Scall (Some _t'1)
        (Evar ___gmpz_cmp (Tfunction
                            (Tcons (tptr (Tstruct __537 noattr))
                              (Tcons (tptr (Tstruct __537 noattr)) Tnil))
                            tint cc_default))
        ((Efield (Evar _l (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) ::
         (Efield (Evar _r (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) :: nil))
      (Sifthenelse (Ebinop Oge (Etempvar _t'1 tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
          (Econst_int (Int.repr 1) tint))
        (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
          (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_interp_blt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr tint)) :: (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Scall (Some _t'1)
        (Evar ___gmpz_cmp (Tfunction
                            (Tcons (tptr (Tstruct __537 noattr))
                              (Tcons (tptr (Tstruct __537 noattr)) Tnil))
                            tint cc_default))
        ((Efield (Evar _l (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) ::
         (Efield (Evar _r (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) :: nil))
      (Sifthenelse (Ebinop Olt (Etempvar _t'1 tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
          (Econst_int (Int.repr 1) tint))
        (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
          (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_interp_bgt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr tint)) :: (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Scall (Some _t'1)
        (Evar ___gmpz_cmp (Tfunction
                            (Tcons (tptr (Tstruct __537 noattr))
                              (Tcons (tptr (Tstruct __537 noattr)) Tnil))
                            tint cc_default))
        ((Efield (Evar _l (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) ::
         (Efield (Evar _r (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) :: nil))
      (Sifthenelse (Ebinop Ogt (Etempvar _t'1 tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
          (Econst_int (Int.repr 1) tint))
        (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
          (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_interp_beq := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr tint)) :: (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Scall (Some _t'1)
        (Evar ___gmpz_cmp (Tfunction
                            (Tcons (tptr (Tstruct __537 noattr))
                              (Tcons (tptr (Tstruct __537 noattr)) Tnil))
                            tint cc_default))
        ((Efield (Evar _l (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) ::
         (Efield (Evar _r (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) :: nil))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
          (Econst_int (Int.repr 1) tint))
        (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
          (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_interp_bne := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr tint)) :: (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Scall (Some _t'1)
        (Evar ___gmpz_cmp (Tfunction
                            (Tcons (tptr (Tstruct __537 noattr))
                              (Tcons (tptr (Tstruct __537 noattr)) Tnil))
                            tint cc_default))
        ((Efield (Evar _l (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) ::
         (Efield (Evar _r (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) :: nil))
      (Sifthenelse (Ebinop One (Etempvar _t'1 tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
          (Econst_int (Int.repr 1) tint))
        (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
          (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_interp_bitwise_and := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Scall None
        (Evar ___gmpz_init (Tfunction
                             (Tcons (tptr (Tstruct __537 noattr)) Tnil) tvoid
                             cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) :: nil))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) _width tint)
          (Efield (Evar _l (Tstruct _BitVec noattr)) _width tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                (Tstruct _BitVec noattr)) _is_signed tint)
            (Efield (Evar _l (Tstruct _BitVec noattr)) _is_signed tint))
          (Scall None
            (Evar ___gmpz_and (Tfunction
                                (Tcons (tptr (Tstruct __537 noattr))
                                  (Tcons (tptr (Tstruct __537 noattr))
                                    (Tcons (tptr (Tstruct __537 noattr))
                                      Tnil))) tvoid cc_default))
            ((Efield
               (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                 (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) ::
             (Efield (Evar _l (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) ::
             (Efield (Evar _r (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) :: nil)))))))
|}.

Definition f_interp_bitwise_xor := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Scall None
        (Evar ___gmpz_init (Tfunction
                             (Tcons (tptr (Tstruct __537 noattr)) Tnil) tvoid
                             cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) :: nil))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) _width tint)
          (Efield (Evar _l (Tstruct _BitVec noattr)) _width tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                (Tstruct _BitVec noattr)) _is_signed tint)
            (Efield (Evar _l (Tstruct _BitVec noattr)) _is_signed tint))
          (Scall None
            (Evar ___gmpz_xor (Tfunction
                                (Tcons (tptr (Tstruct __537 noattr))
                                  (Tcons (tptr (Tstruct __537 noattr))
                                    (Tcons (tptr (Tstruct __537 noattr))
                                      Tnil))) tvoid cc_default))
            ((Efield
               (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                 (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) ::
             (Efield (Evar _l (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) ::
             (Efield (Evar _r (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) :: nil)))))))
|}.

Definition f_interp_bitwise_or := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Scall None
        (Evar ___gmpz_init (Tfunction
                             (Tcons (tptr (Tstruct __537 noattr)) Tnil) tvoid
                             cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) :: nil))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) _width tint)
          (Efield (Evar _l (Tstruct _BitVec noattr)) _width tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                (Tstruct _BitVec noattr)) _is_signed tint)
            (Efield (Evar _l (Tstruct _BitVec noattr)) _is_signed tint))
          (Scall None
            (Evar ___gmpz_ior (Tfunction
                                (Tcons (tptr (Tstruct __537 noattr))
                                  (Tcons (tptr (Tstruct __537 noattr))
                                    (Tcons (tptr (Tstruct __537 noattr))
                                      Tnil))) tvoid cc_default))
            ((Efield
               (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                 (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) ::
             (Efield (Evar _l (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) ::
             (Efield (Evar _r (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) :: nil)))))))
|}.

Definition f_interp_concat := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_left_shifted, (tarray (Tstruct __537 noattr) 1)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
            (Tstruct _BitVec noattr)) _width tint)
        (Ebinop Oadd (Efield (Evar _l (Tstruct _BitVec noattr)) _width tint)
          (Efield (Evar _r (Tstruct _BitVec noattr)) _width tint) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) _is_signed tint)
          (Efield (Evar _l (Tstruct _BitVec noattr)) _is_signed tint))
        (Ssequence
          (Scall None
            (Evar ___gmpz_init (Tfunction
                                 (Tcons (tptr (Tstruct __537 noattr)) Tnil)
                                 tvoid cc_default))
            ((Evar _left_shifted (tarray (Tstruct __537 noattr) 1)) :: nil))
          (Ssequence
            (Scall None
              (Evar ___gmpz_mul_2exp (Tfunction
                                       (Tcons (tptr (Tstruct __537 noattr))
                                         (Tcons (tptr (Tstruct __537 noattr))
                                           (Tcons tulong Tnil))) tvoid
                                       cc_default))
              ((Evar _left_shifted (tarray (Tstruct __537 noattr) 1)) ::
               (Efield (Evar _l (Tstruct _BitVec noattr)) _value
                 (tarray (Tstruct __537 noattr) 1)) ::
               (Ecast (Efield (Evar _r (Tstruct _BitVec noattr)) _width tint)
                 tulong) :: nil))
            (Scall None
              (Evar ___gmpz_add (Tfunction
                                  (Tcons (tptr (Tstruct __537 noattr))
                                    (Tcons (tptr (Tstruct __537 noattr))
                                      (Tcons (tptr (Tstruct __537 noattr))
                                        Tnil))) tvoid cc_default))
              ((Efield
                 (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                   (Tstruct _BitVec noattr)) _value
                 (tarray (Tstruct __537 noattr) 1)) ::
               (Evar _left_shifted (tarray (Tstruct __537 noattr) 1)) ::
               (Efield (Evar _r (Tstruct _BitVec noattr)) _value
                 (tarray (Tstruct __537 noattr) 1)) :: nil))))))))
|}.

Definition f_interp_cast_to_bool := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr tint)) :: (_src, (Tstruct _BitVec noattr)) ::
                nil);
  fn_vars := ((_src, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _src (Tstruct _BitVec noattr))
    (Etempvar _src (Tstruct _BitVec noattr)))
  (Ssequence
    (Scall (Some _t'1)
      (Evar ___gmpz_cmp_si (Tfunction
                             (Tcons (tptr (Tstruct __537 noattr))
                               (Tcons tlong Tnil)) tint cc_default))
      ((Efield (Evar _src (Tstruct _BitVec noattr)) _value
         (tarray (Tstruct __537 noattr) 1)) ::
       (Ecast (Econst_int (Int.repr 0) tint) tlong) :: nil))
    (Sassign (Ederef (Etempvar _dst (tptr tint)) tint) (Etempvar _t'1 tint))))
|}.

Definition f_interp_cast_from_bool := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) :: (_src, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
        (Tstruct _BitVec noattr)) _width tint)
    (Econst_int (Int.repr 1) tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
          (Tstruct _BitVec noattr)) _is_signed tint)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Scall None
        (Evar ___gmpz_init (Tfunction
                             (Tcons (tptr (Tstruct __537 noattr)) Tnil) tvoid
                             cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) :: nil))
      (Scall None
        (Evar ___gmpz_set_si (Tfunction
                               (Tcons (tptr (Tstruct __537 noattr))
                                 (Tcons tlong Tnil)) tvoid cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __537 noattr) 1)) ::
         (Ecast (Etempvar _src tint) tlong) :: nil)))))
|}.

Definition f_interp_cast := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_src, (Tstruct _BitVec noattr)) :: (_t, tint) ::
                (_width, tint) :: nil);
  fn_vars := ((_src, (Tstruct _BitVec noattr)) ::
              (_top, (tarray (Tstruct __537 noattr) 1)) ::
              (_top__1, (tarray (Tstruct __537 noattr) 1)) ::
              (_top__2, (tarray (Tstruct __537 noattr) 1)) :: nil);
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _src (Tstruct _BitVec noattr))
    (Etempvar _src (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
          (Tstruct _BitVec noattr)) _width tint) (Etempvar _width tint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) _is_signed tint)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Scall None
            (Evar ___gmpz_init (Tfunction
                                 (Tcons (tptr (Tstruct __537 noattr)) Tnil)
                                 tvoid cc_default))
            ((Efield
               (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                 (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) :: nil))
          (Sifthenelse (Efield (Evar _src (Tstruct _BitVec noattr))
                         _is_signed tint)
            (Ssequence
              (Scall (Some _t'1)
                (Evar ___gmpz_cmp_si (Tfunction
                                       (Tcons (tptr (Tstruct __537 noattr))
                                         (Tcons tlong Tnil)) tint cc_default))
                ((Efield (Evar _src (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __537 noattr) 1)) ::
                 (Ecast (Econst_int (Int.repr 0) tint) tlong) :: nil))
              (Sifthenelse (Ebinop Olt (Etempvar _t'1 tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Ssequence
                  (Scall None
                    (Evar ___gmpz_init (Tfunction
                                         (Tcons (tptr (Tstruct __537 noattr))
                                           Tnil) tvoid cc_default))
                    ((Evar _top (tarray (Tstruct __537 noattr) 1)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar ___gmpz_ui_pow_ui (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct __537 noattr))
                                                  (Tcons tulong
                                                    (Tcons tulong Tnil)))
                                                tvoid cc_default))
                      ((Evar _top (tarray (Tstruct __537 noattr) 1)) ::
                       (Econst_int (Int.repr 2) tint) ::
                       (Efield
                         (Ederef
                           (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                           (Tstruct _BitVec noattr)) _width tint) :: nil))
                    (Scall None
                      (Evar ___gmpz_add (Tfunction
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              (Tcons
                                                (tptr (Tstruct __537 noattr))
                                                Tnil))) tvoid cc_default))
                      ((Efield
                         (Ederef
                           (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                           (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Efield (Evar _src (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Evar _top (tarray (Tstruct __537 noattr) 1)) :: nil))))
                (Scall None
                  (Evar ___gmpz_set (Tfunction
                                      (Tcons (tptr (Tstruct __537 noattr))
                                        (Tcons (tptr (Tstruct __537 noattr))
                                          Tnil)) tvoid cc_default))
                  ((Efield
                     (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                       (Tstruct _BitVec noattr)) _value
                     (tarray (Tstruct __537 noattr) 1)) ::
                   (Efield (Evar _src (Tstruct _BitVec noattr)) _value
                     (tarray (Tstruct __537 noattr) 1)) :: nil))))
            (Sifthenelse (Ebinop Ogt
                           (Efield (Evar _src (Tstruct _BitVec noattr))
                             _width tint) (Etempvar _width tint) tint)
              (Ssequence
                (Scall None
                  (Evar ___gmpz_init (Tfunction
                                       (Tcons (tptr (Tstruct __537 noattr))
                                         Tnil) tvoid cc_default))
                  ((Evar _top__1 (tarray (Tstruct __537 noattr) 1)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar ___gmpz_ui_pow_ui (Tfunction
                                              (Tcons
                                                (tptr (Tstruct __537 noattr))
                                                (Tcons tulong
                                                  (Tcons tulong Tnil))) tvoid
                                              cc_default))
                    ((Evar _top__1 (tarray (Tstruct __537 noattr) 1)) ::
                     (Econst_int (Int.repr 2) tint) ::
                     (Efield
                       (Ederef
                         (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                         (Tstruct _BitVec noattr)) _width tint) :: nil))
                  (Scall None
                    (Evar ___gmpz_mod (Tfunction
                                        (Tcons (tptr (Tstruct __537 noattr))
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              Tnil))) tvoid cc_default))
                    ((Efield
                       (Ederef
                         (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                         (Tstruct _BitVec noattr)) _value
                       (tarray (Tstruct __537 noattr) 1)) ::
                     (Efield (Evar _src (Tstruct _BitVec noattr)) _value
                       (tarray (Tstruct __537 noattr) 1)) ::
                     (Evar _top__1 (tarray (Tstruct __537 noattr) 1)) :: nil))))
              (Scall None
                (Evar ___gmpz_set (Tfunction
                                    (Tcons (tptr (Tstruct __537 noattr))
                                      (Tcons (tptr (Tstruct __537 noattr))
                                        Tnil)) tvoid cc_default))
                ((Efield
                   (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                     (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __537 noattr) 1)) ::
                 (Efield (Evar _src (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __537 noattr) 1)) :: nil))))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) _is_signed tint)
          (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Scall None
            (Evar ___gmpz_init (Tfunction
                                 (Tcons (tptr (Tstruct __537 noattr)) Tnil)
                                 tvoid cc_default))
            ((Efield
               (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                 (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __537 noattr) 1)) :: nil))
          (Sifthenelse (Efield (Evar _src (Tstruct _BitVec noattr))
                         _is_signed tint)
            (Sifthenelse (Ebinop Ogt
                           (Efield (Evar _src (Tstruct _BitVec noattr))
                             _width tint) (Etempvar _width tint) tint)
              (Ssequence
                (Scall None
                  (Evar ___gmpz_init (Tfunction
                                       (Tcons (tptr (Tstruct __537 noattr))
                                         Tnil) tvoid cc_default))
                  ((Evar _top__2 (tarray (Tstruct __537 noattr) 1)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar ___gmpz_ui_pow_ui (Tfunction
                                              (Tcons
                                                (tptr (Tstruct __537 noattr))
                                                (Tcons tulong
                                                  (Tcons tulong Tnil))) tvoid
                                              cc_default))
                    ((Evar _top__2 (tarray (Tstruct __537 noattr) 1)) ::
                     (Econst_int (Int.repr 2) tint) ::
                     (Etempvar _width tint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar ___gmpz_mod (Tfunction
                                          (Tcons
                                            (tptr (Tstruct __537 noattr))
                                            (Tcons
                                              (tptr (Tstruct __537 noattr))
                                              (Tcons
                                                (tptr (Tstruct __537 noattr))
                                                Tnil))) tvoid cc_default))
                      ((Efield
                         (Ederef
                           (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                           (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Efield (Evar _src (Tstruct _BitVec noattr)) _value
                         (tarray (Tstruct __537 noattr) 1)) ::
                       (Evar _top__2 (tarray (Tstruct __537 noattr) 1)) ::
                       nil))
                    (Scall None
                      (Evar _wrap_around (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _BitVec noattr))
                                             Tnil) tvoid cc_default))
                      ((Etempvar _dst (tptr (Tstruct _BitVec noattr))) ::
                       nil)))))
              (Scall None
                (Evar ___gmpz_set (Tfunction
                                    (Tcons (tptr (Tstruct __537 noattr))
                                      (Tcons (tptr (Tstruct __537 noattr))
                                        Tnil)) tvoid cc_default))
                ((Efield
                   (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                     (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __537 noattr) 1)) ::
                 (Efield (Evar _src (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __537 noattr) 1)) :: nil)))
            Sskip))))))
|}.

Definition f_init_pattern := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pattern, (tptr (Tstruct _Pat noattr))) ::
                (_mask, (Tstruct _BitVec noattr)) ::
                (_val, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_mask, (Tstruct _BitVec noattr)) ::
              (_val, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _mask (Tstruct _BitVec noattr))
    (Etempvar _mask (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _val (Tstruct _BitVec noattr))
      (Etempvar _val (Tstruct _BitVec noattr)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _pattern (tptr (Tstruct _Pat noattr)))
            (Tstruct _Pat noattr)) _mask (Tstruct _BitVec noattr))
        (Evar _mask (Tstruct _BitVec noattr)))
      (Sassign
        (Efield
          (Ederef (Etempvar _pattern (tptr (Tstruct _Pat noattr)))
            (Tstruct _Pat noattr)) _val (Tstruct _BitVec noattr))
        (Evar _val (Tstruct _BitVec noattr))))))
|}.

Definition f_init_action := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_actionRef, (tptr (Tstruct _ActionRef noattr))) ::
                (_action, tint) ::
                (_arguments, (tptr (Tstruct _BitVec noattr))) ::
                (_num_args, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _actionRef (tptr (Tstruct _ActionRef noattr)))
        (Tstruct _ActionRef noattr)) _action tint) (Etempvar _action tint))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
        ((Ebinop Omul (Esizeof (Tstruct _BitVec noattr) tulong)
           (Etempvar _num_args tint) tulong) :: nil))
      (Sassign
        (Efield
          (Ederef (Etempvar _actionRef (tptr (Tstruct _ActionRef noattr)))
            (Tstruct _ActionRef noattr)) _arguments
          (tptr (Tstruct _BitVec noattr)))
        (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _BitVec noattr)))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Etempvar _num_args tint) tint)
              Sskip
              Sbreak)
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _actionRef (tptr (Tstruct _ActionRef noattr)))
                      (Tstruct _ActionRef noattr)) _arguments
                    (tptr (Tstruct _BitVec noattr))) (Etempvar _i tint)
                  (tptr (Tstruct _BitVec noattr))) (Tstruct _BitVec noattr))
              (Ederef
                (Ebinop Oadd
                  (Etempvar _arguments (tptr (Tstruct _BitVec noattr)))
                  (Etempvar _i tint) (tptr (Tstruct _BitVec noattr)))
                (Tstruct _BitVec noattr))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Sassign
        (Efield
          (Ederef (Etempvar _actionRef (tptr (Tstruct _ActionRef noattr)))
            (Tstruct _ActionRef noattr)) _num_args tint)
        (Etempvar _num_args tint)))))
|}.

Definition f_init_entry := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_entry, (tptr (Tstruct _Entry noattr))) ::
                (_pattern, (tptr (Tstruct _Pat noattr))) ::
                (_action, (Tstruct _ActionRef noattr)) ::
                (_num_keys, tint) :: nil);
  fn_vars := ((_action, (Tstruct _ActionRef noattr)) :: nil);
  fn_temps := ((_i, tint) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _action (Tstruct _ActionRef noattr))
    (Etempvar _action (Tstruct _ActionRef noattr)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
        ((Ebinop Omul (Esizeof (Tstruct _Pat noattr) tulong)
           (Etempvar _num_keys tint) tulong) :: nil))
      (Sassign
        (Efield
          (Ederef (Etempvar _entry (tptr (Tstruct _Entry noattr)))
            (Tstruct _Entry noattr)) _pattern (tptr (Tstruct _Pat noattr)))
        (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _Pat noattr)))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Etempvar _num_keys tint) tint)
              Sskip
              Sbreak)
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _entry (tptr (Tstruct _Entry noattr)))
                      (Tstruct _Entry noattr)) _pattern
                    (tptr (Tstruct _Pat noattr))) (Etempvar _i tint)
                  (tptr (Tstruct _Pat noattr))) (Tstruct _Pat noattr))
              (Ederef
                (Ebinop Oadd (Etempvar _pattern (tptr (Tstruct _Pat noattr)))
                  (Etempvar _i tint) (tptr (Tstruct _Pat noattr)))
                (Tstruct _Pat noattr))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Sassign
        (Efield
          (Ederef (Etempvar _entry (tptr (Tstruct _Entry noattr)))
            (Tstruct _Entry noattr)) _action_ref (Tstruct _ActionRef noattr))
        (Evar _action (Tstruct _ActionRef noattr))))))
|}.

Definition f_init_table := {|
  fn_return := (tptr (Tstruct _Table noattr));
  fn_callconv := cc_default;
  fn_params := ((_num_keys, tint) :: (_size, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_table, (tptr (Tstruct _Table noattr))) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _Table noattr) tulong) :: nil))
    (Sset _table
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _Table noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _table (tptr (Tstruct _Table noattr)))
          (Tstruct _Table noattr)) _num_keys tint) (Etempvar _num_keys tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _table (tptr (Tstruct _Table noattr)))
            (Tstruct _Table noattr)) _capacity tint) (Etempvar _size tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _table (tptr (Tstruct _Table noattr)))
              (Tstruct _Table noattr)) _num_entries tint)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Scall (Some _t'2)
            (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                            cc_default))
            ((Ebinop Omul (Esizeof (Tstruct _Entry noattr) tulong)
               (Etempvar _size tint) tulong) :: nil))
          (Sassign
            (Efield
              (Ederef (Etempvar _table (tptr (Tstruct _Table noattr)))
                (Tstruct _Table noattr)) _entries
              (tptr (Tstruct _Entry noattr)))
            (Ecast (Etempvar _t'2 (tptr tvoid))
              (tptr (Tstruct _Entry noattr)))))))))
|}.

Definition f_add_entry := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr (Tstruct _Table noattr))) ::
                (_entry, (Tstruct _Entry noattr)) :: nil);
  fn_vars := ((_entry, (Tstruct _Entry noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _entry (Tstruct _Entry noattr))
    (Etempvar _entry (Tstruct _Entry noattr)))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _table (tptr (Tstruct _Table noattr)))
              (Tstruct _Table noattr)) _entries
            (tptr (Tstruct _Entry noattr)))
          (Efield
            (Ederef (Etempvar _table (tptr (Tstruct _Table noattr)))
              (Tstruct _Table noattr)) _num_entries tint)
          (tptr (Tstruct _Entry noattr))) (Tstruct _Entry noattr))
      (Evar _entry (Tstruct _Entry noattr)))
    (Sassign
      (Efield
        (Ederef (Etempvar _table (tptr (Tstruct _Table noattr)))
          (Tstruct _Table noattr)) _num_entries tint)
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _table (tptr (Tstruct _Table noattr)))
            (Tstruct _Table noattr)) _num_entries tint)
        (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_pattern_match := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr tint)) :: (_pattern, (Tstruct _Pat noattr)) ::
                (_val, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_pattern, (Tstruct _Pat noattr)) ::
              (_val, (Tstruct _BitVec noattr)) ::
              (_val_masked, (Tstruct _BitVec noattr)) ::
              (_key_masked, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _pattern (Tstruct _Pat noattr))
    (Etempvar _pattern (Tstruct _Pat noattr)))
  (Ssequence
    (Sassign (Evar _val (Tstruct _BitVec noattr))
      (Etempvar _val (Tstruct _BitVec noattr)))
    (Ssequence
      (Scall None
        (Evar _interp_bitwise_and (Tfunction
                                    (Tcons (tptr (Tstruct _BitVec noattr))
                                      (Tcons (Tstruct _BitVec noattr)
                                        (Tcons (Tstruct _BitVec noattr) Tnil)))
                                    tvoid cc_default))
        ((Eaddrof (Evar _val_masked (Tstruct _BitVec noattr))
           (tptr (Tstruct _BitVec noattr))) ::
         (Evar _val (Tstruct _BitVec noattr)) ::
         (Efield (Evar _pattern (Tstruct _Pat noattr)) _mask
           (Tstruct _BitVec noattr)) :: nil))
      (Ssequence
        (Scall None
          (Evar _interp_bitwise_and (Tfunction
                                      (Tcons (tptr (Tstruct _BitVec noattr))
                                        (Tcons (Tstruct _BitVec noattr)
                                          (Tcons (Tstruct _BitVec noattr)
                                            Tnil))) tvoid cc_default))
          ((Eaddrof (Evar _key_masked (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Efield (Evar _pattern (Tstruct _Pat noattr)) _val
             (Tstruct _BitVec noattr)) ::
           (Efield (Evar _pattern (Tstruct _Pat noattr)) _mask
             (Tstruct _BitVec noattr)) :: nil))
        (Scall None
          (Evar _interp_bne (Tfunction
                              (Tcons (tptr tint)
                                (Tcons (Tstruct _BitVec noattr)
                                  (Tcons (Tstruct _BitVec noattr) Tnil)))
                              tvoid cc_default))
          ((Etempvar _dst (tptr tint)) ::
           (Evar _val_masked (Tstruct _BitVec noattr)) ::
           (Evar _key_masked (Tstruct _BitVec noattr)) :: nil))))))
|}.

Definition f_entry_match := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr tint)) :: (_entry, (Tstruct _Entry noattr)) ::
                (_val, (tptr (Tstruct _BitVec noattr))) ::
                (_num_keys, tint) :: nil);
  fn_vars := ((_entry, (Tstruct _Entry noattr)) :: nil);
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _entry (Tstruct _Entry noattr))
    (Etempvar _entry (Tstruct _Entry noattr)))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _num_keys tint)
                       tint)
          Sskip
          Sbreak)
        (Ssequence
          (Scall None
            (Evar _pattern_match (Tfunction
                                   (Tcons (tptr tint)
                                     (Tcons (Tstruct _Pat noattr)
                                       (Tcons (Tstruct _BitVec noattr) Tnil)))
                                   tvoid cc_default))
            ((Etempvar _dst (tptr tint)) ::
             (Ederef
               (Ebinop Oadd
                 (Efield (Evar _entry (Tstruct _Entry noattr)) _pattern
                   (tptr (Tstruct _Pat noattr))) (Etempvar _i tint)
                 (tptr (Tstruct _Pat noattr))) (Tstruct _Pat noattr)) ::
             (Ederef
               (Ebinop Oadd (Etempvar _val (tptr (Tstruct _BitVec noattr)))
                 (Etempvar _i tint) (tptr (Tstruct _BitVec noattr)))
               (Tstruct _BitVec noattr)) :: nil))
          (Sifthenelse (Eunop Onotbool
                         (Ederef (Etempvar _dst (tptr tint)) tint) tint)
            (Sreturn None)
            Sskip)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))))
|}.

Definition f_table_match := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _ActionRef noattr))) ::
                (_table, (tptr (Tstruct _Table noattr))) ::
                (_keys, (tptr (Tstruct _BitVec noattr))) :: nil);
  fn_vars := ((_matched, tint) :: nil);
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Ederef (Etempvar _dst (tptr (Tstruct _ActionRef noattr)))
      (Tstruct _ActionRef noattr))
    (Evar _default_action (Tstruct _ActionRef noattr)))
  (Ssequence
    (Sset _i
      (Ebinop Osub
        (Efield
          (Ederef (Etempvar _table (tptr (Tstruct _Table noattr)))
            (Tstruct _Table noattr)) _num_entries tint)
        (Econst_int (Int.repr 1) tint) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                       (Econst_int (Int.repr 0) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Scall None
            (Evar _entry_match (Tfunction
                                 (Tcons (tptr tint)
                                   (Tcons (Tstruct _Entry noattr)
                                     (Tcons (tptr (Tstruct _BitVec noattr))
                                       (Tcons tint Tnil)))) tvoid cc_default))
            ((Eaddrof (Evar _matched tint) (tptr tint)) ::
             (Ederef
               (Ebinop Oadd
                 (Efield
                   (Ederef (Etempvar _table (tptr (Tstruct _Table noattr)))
                     (Tstruct _Table noattr)) _entries
                   (tptr (Tstruct _Entry noattr))) (Etempvar _i tint)
                 (tptr (Tstruct _Entry noattr))) (Tstruct _Entry noattr)) ::
             (Etempvar _keys (tptr (Tstruct _BitVec noattr))) ::
             (Efield
               (Ederef (Etempvar _table (tptr (Tstruct _Table noattr)))
                 (Tstruct _Table noattr)) _num_keys tint) :: nil))
          (Sifthenelse (Evar _matched tint)
            (Ssequence
              (Sassign
                (Ederef (Etempvar _dst (tptr (Tstruct _ActionRef noattr)))
                  (Tstruct _ActionRef noattr))
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _table (tptr (Tstruct _Table noattr)))
                          (Tstruct _Table noattr)) _entries
                        (tptr (Tstruct _Entry noattr))) (Etempvar _i tint)
                      (tptr (Tstruct _Entry noattr)))
                    (Tstruct _Entry noattr)) _action_ref
                  (Tstruct _ActionRef noattr)))
              (Sreturn None))
            Sskip)))
      (Sset _i
        (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))))
|}.

Definition composites : list composite_definition :=
(Composite __537 Struct
   (Member_plain __mp_alloc tint :: Member_plain __mp_size tint ::
    Member_plain __mp_d (tptr tulong) :: nil)
   noattr ::
 Composite _packet_in Struct (Member_plain _in (tptr tuchar) :: nil) noattr ::
 Composite _BitVec Struct
   (Member_plain _is_signed tint :: Member_plain _width tint ::
    Member_plain _value (tarray (Tstruct __537 noattr) 1) :: nil)
   noattr ::
 Composite _Pat Struct
   (Member_plain _mask (Tstruct _BitVec noattr) ::
    Member_plain _val (Tstruct _BitVec noattr) :: nil)
   noattr ::
 Composite _ActionRef Struct
   (Member_plain _action tint ::
    Member_plain _arguments (tptr (Tstruct _BitVec noattr)) ::
    Member_plain _num_args tint :: nil)
   noattr ::
 Composite _Entry Struct
   (Member_plain _pattern (tptr (Tstruct _Pat noattr)) ::
    Member_plain _action_ref (Tstruct _ActionRef noattr) :: nil)
   noattr ::
 Composite _Table Struct
   (Member_plain _num_keys tint :: Member_plain _num_entries tint ::
    Member_plain _capacity tint ::
    Member_plain _entries (tptr (Tstruct _Entry noattr)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) :: (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (___gmpz_add,
   Gfun(External (EF_external "__gmpz_add"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __537 noattr))
       (Tcons (tptr (Tstruct __537 noattr))
         (Tcons (tptr (Tstruct __537 noattr)) Tnil))) tvoid cc_default)) ::
 (___gmpz_and,
   Gfun(External (EF_external "__gmpz_and"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __537 noattr))
       (Tcons (tptr (Tstruct __537 noattr))
         (Tcons (tptr (Tstruct __537 noattr)) Tnil))) tvoid cc_default)) ::
 (___gmpz_clear,
   Gfun(External (EF_external "__gmpz_clear"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __537 noattr)) Tnil) tvoid cc_default)) ::
 (___gmpz_cmp,
   Gfun(External (EF_external "__gmpz_cmp"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tint
                     cc_default))
     (Tcons (tptr (Tstruct __537 noattr))
       (Tcons (tptr (Tstruct __537 noattr)) Tnil)) tint cc_default)) ::
 (___gmpz_cmp_si,
   Gfun(External (EF_external "__gmpz_cmp_si"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tint
                     cc_default))
     (Tcons (tptr (Tstruct __537 noattr)) (Tcons tlong Tnil)) tint
     cc_default)) ::
 (___gmpz_fdiv_q_2exp,
   Gfun(External (EF_external "__gmpz_fdiv_q_2exp"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __537 noattr))
       (Tcons (tptr (Tstruct __537 noattr)) (Tcons tulong Tnil))) tvoid
     cc_default)) ::
 (___gmpz_init,
   Gfun(External (EF_external "__gmpz_init"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __537 noattr)) Tnil) tvoid cc_default)) ::
 (___gmpz_ior,
   Gfun(External (EF_external "__gmpz_ior"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __537 noattr))
       (Tcons (tptr (Tstruct __537 noattr))
         (Tcons (tptr (Tstruct __537 noattr)) Tnil))) tvoid cc_default)) ::
 (___gmpz_mod,
   Gfun(External (EF_external "__gmpz_mod"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __537 noattr))
       (Tcons (tptr (Tstruct __537 noattr))
         (Tcons (tptr (Tstruct __537 noattr)) Tnil))) tvoid cc_default)) ::
 (___gmpz_mul,
   Gfun(External (EF_external "__gmpz_mul"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __537 noattr))
       (Tcons (tptr (Tstruct __537 noattr))
         (Tcons (tptr (Tstruct __537 noattr)) Tnil))) tvoid cc_default)) ::
 (___gmpz_mul_2exp,
   Gfun(External (EF_external "__gmpz_mul_2exp"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __537 noattr))
       (Tcons (tptr (Tstruct __537 noattr)) (Tcons tulong Tnil))) tvoid
     cc_default)) ::
 (___gmpz_neg,
   Gfun(External (EF_external "__gmpz_neg"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct __537 noattr))
       (Tcons (tptr (Tstruct __537 noattr)) Tnil)) tvoid cc_default)) ::
 (___gmpz_set,
   Gfun(External (EF_external "__gmpz_set"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct __537 noattr))
       (Tcons (tptr (Tstruct __537 noattr)) Tnil)) tvoid cc_default)) ::
 (___gmpz_set_si,
   Gfun(External (EF_external "__gmpz_set_si"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct __537 noattr)) (Tcons tlong Tnil)) tvoid
     cc_default)) ::
 (___gmpz_set_str,
   Gfun(External (EF_external "__gmpz_set_str"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tint :: nil)
                     AST.Tint cc_default))
     (Tcons (tptr (Tstruct __537 noattr))
       (Tcons (tptr tschar) (Tcons tint Tnil))) tint cc_default)) ::
 (___gmpz_set_ui,
   Gfun(External (EF_external "__gmpz_set_ui"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct __537 noattr)) (Tcons tulong Tnil)) tvoid
     cc_default)) ::
 (___gmpz_sub,
   Gfun(External (EF_external "__gmpz_sub"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __537 noattr))
       (Tcons (tptr (Tstruct __537 noattr))
         (Tcons (tptr (Tstruct __537 noattr)) Tnil))) tvoid cc_default)) ::
 (___gmpz_sub_ui,
   Gfun(External (EF_external "__gmpz_sub_ui"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __537 noattr))
       (Tcons (tptr (Tstruct __537 noattr)) (Tcons tulong Tnil))) tvoid
     cc_default)) ::
 (___gmpz_ui_pow_ui,
   Gfun(External (EF_external "__gmpz_ui_pow_ui"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __537 noattr)) (Tcons tulong (Tcons tulong Tnil)))
     tvoid cc_default)) ::
 (___gmpz_xor,
   Gfun(External (EF_external "__gmpz_xor"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __537 noattr))
       (Tcons (tptr (Tstruct __537 noattr))
         (Tcons (tptr (Tstruct __537 noattr)) Tnil))) tvoid cc_default)) ::
 (___assert_fail,
   Gfun(External (EF_external "__assert_fail"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tschar)
       (Tcons (tptr tschar) (Tcons tuint (Tcons (tptr tschar) Tnil)))) tvoid
     cc_default)) :: (_default_action, Gvar v_default_action) ::
 (_reset_bitvec, Gfun(Internal f_reset_bitvec)) ::
 (___func__, Gvar v___func__) ::
 (_init_bitvec, Gfun(Internal f_init_bitvec)) ::
 (___func____1, Gvar v___func____1) ::
 (_init_bitvec_binary, Gfun(Internal f_init_bitvec_binary)) ::
 (_extract_bool, Gfun(Internal f_extract_bool)) ::
 (_extract_bitvec, Gfun(Internal f_extract_bitvec)) ::
 (_eval_uminus, Gfun(Internal f_eval_uminus)) ::
 (_interp_uminus, Gfun(Internal f_interp_uminus)) ::
 (_eval_sat_add_sub, Gfun(Internal f_eval_sat_add_sub)) ::
 (_wrap_around, Gfun(Internal f_wrap_around)) ::
 (_interp_bplus, Gfun(Internal f_interp_bplus)) ::
 (_interp_bplus_sat, Gfun(Internal f_interp_bplus_sat)) ::
 (_interp_bminus, Gfun(Internal f_interp_bminus)) ::
 (_interp_bminus_sat, Gfun(Internal f_interp_bminus_sat)) ::
 (_interp_bmult, Gfun(Internal f_interp_bmult)) ::
 (_interp_bmod, Gfun(Internal f_interp_bmod)) ::
 (_interp_bshl, Gfun(Internal f_interp_bshl)) ::
 (_interp_bshr, Gfun(Internal f_interp_bshr)) ::
 (_interp_ble, Gfun(Internal f_interp_ble)) ::
 (_interp_bge, Gfun(Internal f_interp_bge)) ::
 (_interp_blt, Gfun(Internal f_interp_blt)) ::
 (_interp_bgt, Gfun(Internal f_interp_bgt)) ::
 (_interp_beq, Gfun(Internal f_interp_beq)) ::
 (_interp_bne, Gfun(Internal f_interp_bne)) ::
 (_interp_bitwise_and, Gfun(Internal f_interp_bitwise_and)) ::
 (_interp_bitwise_xor, Gfun(Internal f_interp_bitwise_xor)) ::
 (_interp_bitwise_or, Gfun(Internal f_interp_bitwise_or)) ::
 (_interp_concat, Gfun(Internal f_interp_concat)) ::
 (_interp_cast_to_bool, Gfun(Internal f_interp_cast_to_bool)) ::
 (_interp_cast_from_bool, Gfun(Internal f_interp_cast_from_bool)) ::
 (_interp_cast, Gfun(Internal f_interp_cast)) ::
 (_init_pattern, Gfun(Internal f_init_pattern)) ::
 (_init_action, Gfun(Internal f_init_action)) ::
 (_init_entry, Gfun(Internal f_init_entry)) ::
 (_init_table, Gfun(Internal f_init_table)) ::
 (_add_entry, Gfun(Internal f_add_entry)) ::
 (_pattern_match, Gfun(Internal f_pattern_match)) ::
 (_entry_match, Gfun(Internal f_entry_match)) ::
 (_table_match, Gfun(Internal f_table_match)) :: nil).

Definition public_idents : list ident :=
(_table_match :: _entry_match :: _pattern_match :: _add_entry ::
 _init_table :: _init_entry :: _init_action :: _init_pattern ::
 _interp_cast :: _interp_cast_from_bool :: _interp_cast_to_bool ::
 _interp_concat :: _interp_bitwise_or :: _interp_bitwise_xor ::
 _interp_bitwise_and :: _interp_bne :: _interp_beq :: _interp_bgt ::
 _interp_blt :: _interp_bge :: _interp_ble :: _interp_bshr :: _interp_bshl ::
 _interp_bmod :: _interp_bmult :: _interp_bminus_sat :: _interp_bminus ::
 _interp_bplus_sat :: _interp_bplus :: _wrap_around :: _eval_sat_add_sub ::
 _interp_uminus :: _eval_uminus :: _extract_bitvec :: _extract_bool ::
 _init_bitvec_binary :: _init_bitvec :: _reset_bitvec :: _default_action ::
 ___assert_fail :: ___gmpz_xor :: ___gmpz_ui_pow_ui :: ___gmpz_sub_ui ::
 ___gmpz_sub :: ___gmpz_set_ui :: ___gmpz_set_str :: ___gmpz_set_si ::
 ___gmpz_set :: ___gmpz_neg :: ___gmpz_mul_2exp :: ___gmpz_mul ::
 ___gmpz_mod :: ___gmpz_ior :: ___gmpz_init :: ___gmpz_fdiv_q_2exp ::
 ___gmpz_cmp_si :: ___gmpz_cmp :: ___gmpz_clear :: ___gmpz_and ::
 ___gmpz_add :: _malloc :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


