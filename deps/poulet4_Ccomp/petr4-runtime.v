From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.9".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "petr4-runtime.c".
  Definition normalized := false.
End Info.

Definition _ActionRef : ident := $"ActionRef".
Definition _BitVec : ident := $"BitVec".
Definition _Entry : ident := $"Entry".
Definition _Pat : ident := $"Pat".
Definition _Table : ident := $"Table".
Definition __585 : ident := $"_585".
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
Definition ___gmpz_add : ident := $"__gmpz_add".
Definition ___gmpz_and : ident := $"__gmpz_and".
Definition ___gmpz_cdiv_q : ident := $"__gmpz_cdiv_q".
Definition ___gmpz_clear : ident := $"__gmpz_clear".
Definition ___gmpz_cmp : ident := $"__gmpz_cmp".
Definition ___gmpz_cmp_d : ident := $"__gmpz_cmp_d".
Definition ___gmpz_fdiv_q_2exp : ident := $"__gmpz_fdiv_q_2exp".
Definition ___gmpz_fdiv_r_ui : ident := $"__gmpz_fdiv_r_ui".
Definition ___gmpz_init : ident := $"__gmpz_init".
Definition ___gmpz_ior : ident := $"__gmpz_ior".
Definition ___gmpz_mod : ident := $"__gmpz_mod".
Definition ___gmpz_mul : ident := $"__gmpz_mul".
Definition ___gmpz_mul_2exp : ident := $"__gmpz_mul_2exp".
Definition ___gmpz_neg : ident := $"__gmpz_neg".
Definition ___gmpz_set : ident := $"__gmpz_set".
Definition ___gmpz_set_str : ident := $"__gmpz_set_str".
Definition ___gmpz_set_ui : ident := $"__gmpz_set_ui".
Definition ___gmpz_sub : ident := $"__gmpz_sub".
Definition ___gmpz_tdiv_q_2exp : ident := $"__gmpz_tdiv_q_2exp".
Definition ___gmpz_xor : ident := $"__gmpz_xor".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition __mp_alloc : ident := $"_mp_alloc".
Definition __mp_d : ident := $"_mp_d".
Definition __mp_size : ident := $"_mp_size".
Definition __res : ident := $"_res".
Definition _action : ident := $"action".
Definition _actionRef : ident := $"actionRef".
Definition _action_ref : ident := $"action_ref".
Definition _add_entry : ident := $"add_entry".
Definition _args_lub : ident := $"args_lub".
Definition _arguments : ident := $"arguments".
Definition _capacity : ident := $"capacity".
Definition _check : ident := $"check".
Definition _dst : ident := $"dst".
Definition _dst_value : ident := $"dst_value".
Definition _entries : ident := $"entries".
Definition _entry : ident := $"entry".
Definition _eval_sat_add_sub : ident := $"eval_sat_add_sub".
Definition _eval_uminus : ident := $"eval_uminus".
Definition _i : ident := $"i".
Definition _init_Entry : ident := $"init_Entry".
Definition _init_action : ident := $"init_action".
Definition _init_bitvec : ident := $"init_bitvec".
Definition _init_interp_binary_op : ident := $"init_interp_binary_op".
Definition _init_pattern : ident := $"init_pattern".
Definition _init_table : ident := $"init_table".
Definition _interp_band : ident := $"interp_band".
Definition _interp_bdiv : ident := $"interp_bdiv".
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
Definition _interp_bor : ident := $"interp_bor".
Definition _interp_bplus : ident := $"interp_bplus".
Definition _interp_bplus_sat : ident := $"interp_bplus_sat".
Definition _interp_bshl : ident := $"interp_bshl".
Definition _interp_bshr : ident := $"interp_bshr".
Definition _is_add : ident := $"is_add".
Definition _is_signed : ident := $"is_signed".
Definition _keys : ident := $"keys".
Definition _l : ident := $"l".
Definition _main : ident := $"main".
Definition _malloc : ident := $"malloc".
Definition _mask : ident := $"mask".
Definition _num_args : ident := $"num_args".
Definition _num_entries : ident := $"num_entries".
Definition _num_keys : ident := $"num_keys".
Definition _pattern : ident := $"pattern".
Definition _pow : ident := $"pow".
Definition _r : ident := $"r".
Definition _reset_bitvec : ident := $"reset_bitvec".
Definition _sign : ident := $"sign".
Definition _size : ident := $"size".
Definition _table : ident := $"table".
Definition _table_match : ident := $"table_match".
Definition _v : ident := $"v".
Definition _val : ident := $"val".
Definition _value : ident := $"value".
Definition _w : ident := $"w".
Definition _width : ident := $"width".
Definition _x : ident := $"x".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 16);
  gvar_init := (Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 0) :: nil);
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

Definition f_reset_bitvec := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct __585 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar ___gmpz_clear (Tfunction (Tcons (tptr (Tstruct __585 noattr)) Tnil)
                        tvoid cc_default))
  ((Etempvar _x (tptr (Tstruct __585 noattr))) :: nil))
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
  fn_vars := ((_i, (tarray (Tstruct __585 noattr) 1)) :: nil);
  fn_temps := ((_check, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar ___gmpz_init (Tfunction (Tcons (tptr (Tstruct __585 noattr)) Tnil)
                         tvoid cc_default))
    ((Evar _i (tarray (Tstruct __585 noattr) 1)) :: nil))
  (Ssequence
    (Scall None
      (Evar ___gmpz_set_ui (Tfunction
                             (Tcons (tptr (Tstruct __585 noattr))
                               (Tcons tulong Tnil)) tvoid cc_default))
      ((Evar _i (tarray (Tstruct __585 noattr) 1)) ::
       (Econst_int (Int.repr 0) tint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar ___gmpz_set_str (Tfunction
                                  (Tcons (tptr (Tstruct __585 noattr))
                                    (Tcons (tptr tschar) (Tcons tint Tnil)))
                                  tint cc_default))
          ((Evar _i (tarray (Tstruct __585 noattr) 1)) ::
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
             (Evar ___stringlit_1 (tarray tschar 16)) ::
             (Econst_int (Int.repr 93) tint) ::
             (Evar ___func__ (tarray tschar 12)) :: nil)))
        (Scall None
          (Evar ___gmpz_set (Tfunction
                              (Tcons (tptr (Tstruct __585 noattr))
                                (Tcons (tptr (Tstruct __585 noattr)) Tnil))
                              tvoid cc_default))
          ((Efield
             (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
               (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Evar _i (tarray (Tstruct __585 noattr) 1)) :: nil))))))
|}.

Definition f_eval_uminus := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (Tstruct __585 noattr))) :: nil);
  fn_vars := ((_dst_value, (tarray (Tstruct __585 noattr) 1)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar ___gmpz_init (Tfunction (Tcons (tptr (Tstruct __585 noattr)) Tnil)
                         tvoid cc_default))
    ((Evar _dst_value (tarray (Tstruct __585 noattr) 1)) :: nil))
  (Ssequence
    (Scall None
      (Evar ___gmpz_set_ui (Tfunction
                             (Tcons (tptr (Tstruct __585 noattr))
                               (Tcons tulong Tnil)) tvoid cc_default))
      ((Evar _dst_value (tarray (Tstruct __585 noattr) 1)) ::
       (Econst_int (Int.repr 0) tint) :: nil))
    (Scall None
      (Evar ___gmpz_neg (Tfunction
                          (Tcons (tptr (Tstruct __585 noattr))
                            (Tcons (tptr (Tstruct __585 noattr)) Tnil)) tvoid
                          cc_default))
      ((Evar _dst_value (tarray (Tstruct __585 noattr) 1)) ::
       (Etempvar _v (tptr (Tstruct __585 noattr))) :: nil))))
|}.

Definition f_eval_sat_add_sub := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: (_is_add, tint) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := ((_t'2, tint) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Efield (Evar _l (Tstruct _BitVec noattr)) _is_signed
                       tint) (Econst_int (Int.repr 1) tint) tint)
        (Sset _t'2
          (Ecast
            (Ebinop Oeq
              (Efield (Evar _r (Tstruct _BitVec noattr)) _is_signed tint)
              (Econst_int (Int.repr 1) tint) tint) tbool))
        (Sset _t'2 (Econst_int (Int.repr 0) tint)))
      (Sifthenelse (Etempvar _t'2 tint)
        (Ssequence
          (Scall None
            (Evar ___gmpz_mul (Tfunction
                                (Tcons (tptr (Tstruct __585 noattr))
                                  (Tcons (tptr (Tstruct __585 noattr))
                                    (Tcons (tptr (Tstruct __585 noattr))
                                      Tnil))) tvoid cc_default))
            ((Efield (Evar _r (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __585 noattr) 1)) ::
             (Efield (Evar _r (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __585 noattr) 1)) ::
             (Etempvar _is_add tint) :: nil))
          (Ssequence
            (Scall None
              (Evar ___gmpz_add (Tfunction
                                  (Tcons (tptr (Tstruct __585 noattr))
                                    (Tcons (tptr (Tstruct __585 noattr))
                                      (Tcons (tptr (Tstruct __585 noattr))
                                        Tnil))) tvoid cc_default))
              ((Efield
                 (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                   (Tstruct _BitVec noattr)) _value
                 (tarray (Tstruct __585 noattr) 1)) ::
               (Efield (Evar _l (Tstruct _BitVec noattr)) _value
                 (tarray (Tstruct __585 noattr) 1)) ::
               (Efield (Evar _r (Tstruct _BitVec noattr)) _value
                 (tarray (Tstruct __585 noattr) 1)) :: nil))
            (Scall None
              (Evar ___gmpz_fdiv_r_ui (Tfunction
                                        (Tcons (tptr (Tstruct __585 noattr))
                                          (Tcons
                                            (tptr (Tstruct __585 noattr))
                                            (Tcons tulong Tnil))) tulong
                                        cc_default))
              ((Efield
                 (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                   (Tstruct _BitVec noattr)) _value
                 (tarray (Tstruct __585 noattr) 1)) ::
               (Efield
                 (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                   (Tstruct _BitVec noattr)) _value
                 (tarray (Tstruct __585 noattr) 1)) ::
               (Efield
                 (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                   (Tstruct _BitVec noattr)) _width tint) :: nil))))
        (Ssequence
          (Scall None
            (Evar ___gmpz_mul (Tfunction
                                (Tcons (tptr (Tstruct __585 noattr))
                                  (Tcons (tptr (Tstruct __585 noattr))
                                    (Tcons (tptr (Tstruct __585 noattr))
                                      Tnil))) tvoid cc_default))
            ((Efield (Evar _r (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __585 noattr) 1)) ::
             (Efield (Evar _r (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __585 noattr) 1)) ::
             (Etempvar _is_add tint) :: nil))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                  (Tstruct _BitVec noattr)) _is_signed tint)
              (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Scall None
                (Evar ___gmpz_add (Tfunction
                                    (Tcons (tptr (Tstruct __585 noattr))
                                      (Tcons (tptr (Tstruct __585 noattr))
                                        (Tcons (tptr (Tstruct __585 noattr))
                                          Tnil))) tvoid cc_default))
                ((Efield
                   (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                     (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __585 noattr) 1)) ::
                 (Efield (Evar _l (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __585 noattr) 1)) ::
                 (Efield (Evar _r (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __585 noattr) 1)) :: nil))
              (Ssequence
                (Scall (Some _t'1)
                  (Evar _pow (Tfunction (Tcons tdouble (Tcons tdouble Tnil))
                               tdouble cc_default))
                  ((Econst_float (Float.of_bits (Int64.repr 4611686018427387904)) tdouble) ::
                   (Ecast
                     (Efield
                       (Ederef
                         (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                         (Tstruct _BitVec noattr)) _width tint) tdouble) ::
                   nil))
                (Scall None
                  (Evar ___gmpz_fdiv_r_ui (Tfunction
                                            (Tcons
                                              (tptr (Tstruct __585 noattr))
                                              (Tcons
                                                (tptr (Tstruct __585 noattr))
                                                (Tcons tulong Tnil))) tulong
                                            cc_default))
                  ((Efield
                     (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                       (Tstruct _BitVec noattr)) _value
                     (tarray (Tstruct __585 noattr) 1)) ::
                   (Efield
                     (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                       (Tstruct _BitVec noattr)) _value
                     (tarray (Tstruct __585 noattr) 1)) ::
                   (Ebinop Osub (Ecast (Etempvar _t'1 tdouble) tint)
                     (Econst_int (Int.repr 1) tint) tint) :: nil))))))))))
|}.

Definition f_init_interp_binary_op := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_dst_value, (tarray (Tstruct __585 noattr) 1)) ::
              (_dst, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Scall None
      (Evar ___gmpz_init (Tfunction
                           (Tcons (tptr (Tstruct __585 noattr)) Tnil) tvoid
                           cc_default))
      ((Evar _dst_value (tarray (Tstruct __585 noattr) 1)) :: nil))
    (Ssequence
      (Scall None
        (Evar ___gmpz_set_ui (Tfunction
                               (Tcons (tptr (Tstruct __585 noattr))
                                 (Tcons tulong Tnil)) tvoid cc_default))
        ((Evar _dst_value (tarray (Tstruct __585 noattr) 1)) ::
         (Econst_int (Int.repr 0) tint) :: nil))
      (Ssequence
        (Sassign
          (Efield (Evar _dst (Tstruct _BitVec noattr)) _is_signed tint)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign (Efield (Evar _dst (Tstruct _BitVec noattr)) _width tint)
            (Efield (Evar _l (Tstruct _BitVec noattr)) _width tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Efield (Evar _dst (Tstruct _BitVec noattr)) _value
                      (tarray (Tstruct __585 noattr) 1))
                    (Econst_int (Int.repr 0) tint)
                    (tptr (Tstruct __585 noattr))) (Tstruct __585 noattr))
                __mp_alloc tint)
              (Evar _dst_value (tarray (Tstruct __585 noattr) 1)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield (Evar _dst (Tstruct _BitVec noattr)) _value
                        (tarray (Tstruct __585 noattr) 1))
                      (Econst_int (Int.repr 0) tint)
                      (tptr (Tstruct __585 noattr))) (Tstruct __585 noattr))
                  __mp_size tint) (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Efield (Evar _dst (Tstruct _BitVec noattr)) _value
                          (tarray (Tstruct __585 noattr) 1))
                        (Econst_int (Int.repr 0) tint)
                        (tptr (Tstruct __585 noattr)))
                      (Tstruct __585 noattr)) __mp_d (tptr tulong))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                (Ssequence
                  (Sassign
                    (Ederef (Etempvar __res (tptr (Tstruct _BitVec noattr)))
                      (Tstruct _BitVec noattr))
                    (Evar _dst (Tstruct _BitVec noattr)))
                  (Sreturn None))))))))))
|}.

Definition f_interp_bplus := {|
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
        (Evar ___gmpz_add (Tfunction
                            (Tcons (tptr (Tstruct __585 noattr))
                              (Tcons (tptr (Tstruct __585 noattr))
                                (Tcons (tptr (Tstruct __585 noattr)) Tnil)))
                            tvoid cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield (Evar _l (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield (Evar _r (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) :: nil))
      (Scall None
        (Evar ___gmpz_fdiv_r_ui (Tfunction
                                  (Tcons (tptr (Tstruct __585 noattr))
                                    (Tcons (tptr (Tstruct __585 noattr))
                                      (Tcons tulong Tnil))) tulong
                                  cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _width tint) :: nil)))))
|}.

Definition f_interp_bplus_sat := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
              (_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _dst (tptr (Tstruct _BitVec noattr)))
    (Etempvar _dst (tptr (Tstruct _BitVec noattr))))
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
                                        (Tcons tint Tnil)))) tvoid
                                  cc_default))
        ((Eaddrof (Evar _dst (tptr (Tstruct _BitVec noattr)))
           (tptr (tptr (Tstruct _BitVec noattr)))) ::
         (Evar _l (Tstruct _BitVec noattr)) ::
         (Evar _r (Tstruct _BitVec noattr)) ::
         (Econst_int (Int.repr 1) tint) :: nil)))))
|}.

Definition f_interp_bminus := {|
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
        (Evar ___gmpz_sub (Tfunction
                            (Tcons (tptr (Tstruct __585 noattr))
                              (Tcons (tptr (Tstruct __585 noattr))
                                (Tcons (tptr (Tstruct __585 noattr)) Tnil)))
                            tvoid cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield (Evar _l (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield (Evar _r (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) :: nil))
      (Scall None
        (Evar ___gmpz_fdiv_r_ui (Tfunction
                                  (Tcons (tptr (Tstruct __585 noattr))
                                    (Tcons (tptr (Tstruct __585 noattr))
                                      (Tcons tulong Tnil))) tulong
                                  cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _width tint) :: nil)))))
|}.

Definition f_interp_bminus_sat := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
              (_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _dst (tptr (Tstruct _BitVec noattr)))
    (Etempvar _dst (tptr (Tstruct _BitVec noattr))))
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
                                        (Tcons tint Tnil)))) tvoid
                                  cc_default))
        ((Eaddrof (Evar _dst (tptr (Tstruct _BitVec noattr)))
           (tptr (tptr (Tstruct _BitVec noattr)))) ::
         (Evar _l (Tstruct _BitVec noattr)) ::
         (Evar _r (Tstruct _BitVec noattr)) ::
         (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) :: nil)))))
|}.

Definition f_interp_bmult := {|
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
        (Evar ___gmpz_mul (Tfunction
                            (Tcons (tptr (Tstruct __585 noattr))
                              (Tcons (tptr (Tstruct __585 noattr))
                                (Tcons (tptr (Tstruct __585 noattr)) Tnil)))
                            tvoid cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield (Evar _l (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield (Evar _r (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) :: nil))
      (Scall None
        (Evar ___gmpz_fdiv_r_ui (Tfunction
                                  (Tcons (tptr (Tstruct __585 noattr))
                                    (Tcons (tptr (Tstruct __585 noattr))
                                      (Tcons tulong Tnil))) tulong
                                  cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _width tint) :: nil)))))
|}.

Definition f_interp_bdiv := {|
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
        (Evar ___gmpz_cdiv_q (Tfunction
                               (Tcons (tptr (Tstruct __585 noattr))
                                 (Tcons (tptr (Tstruct __585 noattr))
                                   (Tcons (tptr (Tstruct __585 noattr)) Tnil)))
                               tvoid cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield (Evar _l (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield (Evar _r (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) :: nil))
      (Scall None
        (Evar ___gmpz_fdiv_r_ui (Tfunction
                                  (Tcons (tptr (Tstruct __585 noattr))
                                    (Tcons (tptr (Tstruct __585 noattr))
                                      (Tcons tulong Tnil))) tulong
                                  cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _width tint) :: nil)))))
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
    (Scall None
      (Evar ___gmpz_mod (Tfunction
                          (Tcons (tptr (Tstruct __585 noattr))
                            (Tcons (tptr (Tstruct __585 noattr))
                              (Tcons (tptr (Tstruct __585 noattr)) Tnil)))
                          tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
           (Tstruct _BitVec noattr)) _value
         (tarray (Tstruct __585 noattr) 1)) ::
       (Efield (Evar _l (Tstruct _BitVec noattr)) _value
         (tarray (Tstruct __585 noattr) 1)) ::
       (Efield (Evar _r (Tstruct _BitVec noattr)) _value
         (tarray (Tstruct __585 noattr) 1)) :: nil))))
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
    (Scall None
      (Evar ___gmpz_mul_2exp (Tfunction
                               (Tcons (tptr (Tstruct __585 noattr))
                                 (Tcons (tptr (Tstruct __585 noattr))
                                   (Tcons tulong Tnil))) tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
           (Tstruct _BitVec noattr)) _value
         (tarray (Tstruct __585 noattr) 1)) ::
       (Efield (Evar _l (Tstruct _BitVec noattr)) _value
         (tarray (Tstruct __585 noattr) 1)) ::
       (Efield (Evar _r (Tstruct _BitVec noattr)) _value
         (tarray (Tstruct __585 noattr) 1)) :: nil))))
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
    (Sifthenelse (Efield
                   (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                     (Tstruct _BitVec noattr)) _is_signed tint)
      (Scall None
        (Evar ___gmpz_fdiv_q_2exp (Tfunction
                                    (Tcons (tptr (Tstruct __585 noattr))
                                      (Tcons (tptr (Tstruct __585 noattr))
                                        (Tcons tulong Tnil))) tvoid
                                    cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield (Evar _l (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield (Evar _r (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) :: nil))
      (Scall None
        (Evar ___gmpz_tdiv_q_2exp (Tfunction
                                    (Tcons (tptr (Tstruct __585 noattr))
                                      (Tcons (tptr (Tstruct __585 noattr))
                                        (Tcons tulong Tnil))) tvoid
                                    cc_default))
        ((Efield
           (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
             (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield (Evar _l (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) ::
         (Efield (Evar _r (Tstruct _BitVec noattr)) _value
           (tarray (Tstruct __585 noattr) 1)) :: nil)))))
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
      (Ssequence
        (Scall (Some _t'1)
          (Evar ___gmpz_cmp (Tfunction
                              (Tcons (tptr (Tstruct __585 noattr))
                                (Tcons (tptr (Tstruct __585 noattr)) Tnil))
                              tint cc_default))
          ((Efield (Evar _l (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _r (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) :: nil))
        (Sifthenelse (Ebinop Ole (Etempvar _t'1 tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
            (Econst_int (Int.repr 1) tint))
          Sskip))
      (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
        (Econst_int (Int.repr 0) tint)))))
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
      (Ssequence
        (Scall (Some _t'1)
          (Evar ___gmpz_cmp (Tfunction
                              (Tcons (tptr (Tstruct __585 noattr))
                                (Tcons (tptr (Tstruct __585 noattr)) Tnil))
                              tint cc_default))
          ((Efield (Evar _l (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _r (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) :: nil))
        (Sifthenelse (Ebinop Oge (Etempvar _t'1 tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
            (Econst_int (Int.repr 1) tint))
          Sskip))
      (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
        (Econst_int (Int.repr 0) tint)))))
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
      (Ssequence
        (Scall (Some _t'1)
          (Evar ___gmpz_cmp (Tfunction
                              (Tcons (tptr (Tstruct __585 noattr))
                                (Tcons (tptr (Tstruct __585 noattr)) Tnil))
                              tint cc_default))
          ((Efield (Evar _l (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _r (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) :: nil))
        (Sifthenelse (Ebinop Olt (Etempvar _t'1 tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
            (Econst_int (Int.repr 1) tint))
          Sskip))
      (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
        (Econst_int (Int.repr 0) tint)))))
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
      (Ssequence
        (Scall (Some _t'1)
          (Evar ___gmpz_cmp (Tfunction
                              (Tcons (tptr (Tstruct __585 noattr))
                                (Tcons (tptr (Tstruct __585 noattr)) Tnil))
                              tint cc_default))
          ((Efield (Evar _l (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _r (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) :: nil))
        (Sifthenelse (Ebinop Ogt (Etempvar _t'1 tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
            (Econst_int (Int.repr 1) tint))
          Sskip))
      (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
        (Econst_int (Int.repr 0) tint)))))
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
      (Ssequence
        (Scall (Some _t'1)
          (Evar ___gmpz_cmp (Tfunction
                              (Tcons (tptr (Tstruct __585 noattr))
                                (Tcons (tptr (Tstruct __585 noattr)) Tnil))
                              tint cc_default))
          ((Efield (Evar _l (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _r (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) :: nil))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
            (Econst_int (Int.repr 1) tint))
          Sskip))
      (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
        (Econst_int (Int.repr 0) tint)))))
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
      (Ssequence
        (Scall (Some _t'1)
          (Evar ___gmpz_cmp (Tfunction
                              (Tcons (tptr (Tstruct __585 noattr))
                                (Tcons (tptr (Tstruct __585 noattr)) Tnil))
                              tint cc_default))
          ((Efield (Evar _l (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _r (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) :: nil))
        (Sifthenelse (Ebinop One (Etempvar _t'1 tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
            (Econst_int (Int.repr 1) tint))
          Sskip))
      (Sassign (Ederef (Etempvar _dst (tptr tint)) tint)
        (Econst_int (Int.repr 0) tint)))))
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
    (Scall None
      (Evar ___gmpz_and (Tfunction
                          (Tcons (tptr (Tstruct __585 noattr))
                            (Tcons (tptr (Tstruct __585 noattr))
                              (Tcons (tptr (Tstruct __585 noattr)) Tnil)))
                          tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
           (Tstruct _BitVec noattr)) _value
         (tarray (Tstruct __585 noattr) 1)) ::
       (Efield (Evar _l (Tstruct _BitVec noattr)) _value
         (tarray (Tstruct __585 noattr) 1)) ::
       (Efield (Evar _r (Tstruct _BitVec noattr)) _value
         (tarray (Tstruct __585 noattr) 1)) :: nil))))
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
    (Scall None
      (Evar ___gmpz_xor (Tfunction
                          (Tcons (tptr (Tstruct __585 noattr))
                            (Tcons (tptr (Tstruct __585 noattr))
                              (Tcons (tptr (Tstruct __585 noattr)) Tnil)))
                          tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
           (Tstruct _BitVec noattr)) _value
         (tarray (Tstruct __585 noattr) 1)) ::
       (Efield (Evar _l (Tstruct _BitVec noattr)) _value
         (tarray (Tstruct __585 noattr) 1)) ::
       (Efield (Evar _r (Tstruct _BitVec noattr)) _value
         (tarray (Tstruct __585 noattr) 1)) :: nil))))
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
    (Scall None
      (Evar ___gmpz_ior (Tfunction
                          (Tcons (tptr (Tstruct __585 noattr))
                            (Tcons (tptr (Tstruct __585 noattr))
                              (Tcons (tptr (Tstruct __585 noattr)) Tnil)))
                          tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
           (Tstruct _BitVec noattr)) _value
         (tarray (Tstruct __585 noattr) 1)) ::
       (Efield (Evar _l (Tstruct _BitVec noattr)) _value
         (tarray (Tstruct __585 noattr) 1)) ::
       (Efield (Evar _r (Tstruct _BitVec noattr)) _value
         (tarray (Tstruct __585 noattr) 1)) :: nil))))
|}.

Definition f_interp_band := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := ((_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar ___gmpz_cmp_d (Tfunction
                                  (Tcons (tptr (Tstruct __585 noattr))
                                    (Tcons tdouble Tnil)) tint cc_default))
            ((Efield (Evar _l (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __585 noattr) 1)) ::
             (Econst_float (Float.of_bits (Int64.repr 0)) tdouble) :: nil))
          (Sifthenelse (Ebinop One (Etempvar _t'1 tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sset _t'2 (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Scall (Some _t'3)
                (Evar ___gmpz_cmp_d (Tfunction
                                      (Tcons (tptr (Tstruct __585 noattr))
                                        (Tcons tdouble Tnil)) tint
                                      cc_default))
                ((Efield (Evar _r (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __585 noattr) 1)) ::
                 (Econst_float (Float.of_bits (Int64.repr 0)) tdouble) ::
                 nil))
              (Sset _t'2
                (Ecast
                  (Ebinop One (Etempvar _t'3 tint)
                    (Econst_int (Int.repr 0) tint) tint) tbool)))))
        (Sifthenelse (Etempvar _t'2 tint)
          (Sreturn (Some (Econst_int (Int.repr 1) tint)))
          Sskip))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_interp_bor := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _BitVec noattr))) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := ((_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar ___gmpz_cmp_d (Tfunction
                                  (Tcons (tptr (Tstruct __585 noattr))
                                    (Tcons tdouble Tnil)) tint cc_default))
            ((Efield (Evar _l (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __585 noattr) 1)) ::
             (Econst_float (Float.of_bits (Int64.repr 0)) tdouble) :: nil))
          (Sifthenelse (Ebinop One (Etempvar _t'1 tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Ssequence
              (Scall (Some _t'3)
                (Evar ___gmpz_cmp_d (Tfunction
                                      (Tcons (tptr (Tstruct __585 noattr))
                                        (Tcons tdouble Tnil)) tint
                                      cc_default))
                ((Efield (Evar _r (Tstruct _BitVec noattr)) _value
                   (tarray (Tstruct __585 noattr) 1)) ::
                 (Econst_float (Float.of_bits (Int64.repr 0)) tdouble) ::
                 nil))
              (Sset _t'2
                (Ecast
                  (Ebinop One (Etempvar _t'3 tint)
                    (Econst_int (Int.repr 0) tint) tint) tbool)))
            (Sset _t'2 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'2 tint)
          (Sreturn (Some (Econst_int (Int.repr 1) tint)))
          Sskip))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_init_pattern := {|
  fn_return := (tptr (Tstruct _Pat noattr));
  fn_callconv := cc_default;
  fn_params := ((_mask, (Tstruct _BitVec noattr)) ::
                (_val, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_mask, (Tstruct _BitVec noattr)) ::
              (_val, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := ((_pattern, (tptr (Tstruct _Pat noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _mask (Tstruct _BitVec noattr))
    (Etempvar _mask (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _val (Tstruct _BitVec noattr))
      (Etempvar _val (Tstruct _BitVec noattr)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                          cc_default))
          ((Esizeof (Tstruct _Pat noattr) tulong) :: nil))
        (Sset _pattern
          (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _Pat noattr)))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _pattern (tptr (Tstruct _Pat noattr)))
              (Tstruct _Pat noattr)) _mask (Tstruct _BitVec noattr))
          (Evar _mask (Tstruct _BitVec noattr)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _pattern (tptr (Tstruct _Pat noattr)))
                (Tstruct _Pat noattr)) _val (Tstruct _BitVec noattr))
            (Evar _val (Tstruct _BitVec noattr)))
          (Sreturn (Some (Etempvar _pattern (tptr (Tstruct _Pat noattr))))))))))
|}.

Definition f_init_action := {|
  fn_return := (tptr (Tstruct _ActionRef noattr));
  fn_callconv := cc_default;
  fn_params := ((_action, tint) ::
                (_arguments, (tptr (Tstruct _BitVec noattr))) ::
                (_num_args, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_actionRef, (tptr (Tstruct _ActionRef noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _ActionRef noattr) tulong) :: nil))
    (Sset _actionRef
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _ActionRef noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _actionRef (tptr (Tstruct _ActionRef noattr)))
          (Tstruct _ActionRef noattr)) _action tint) (Etempvar _action tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _actionRef (tptr (Tstruct _ActionRef noattr)))
            (Tstruct _ActionRef noattr)) _arguments
          (tptr (Tstruct _BitVec noattr)))
        (Etempvar _arguments (tptr (Tstruct _BitVec noattr))))
      (Sassign
        (Efield
          (Ederef (Etempvar _actionRef (tptr (Tstruct _ActionRef noattr)))
            (Tstruct _ActionRef noattr)) _num_args tint)
        (Etempvar _num_args tint)))))
|}.

Definition f_init_Entry := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_entry, (tptr (Tstruct _Entry noattr))) ::
                (_pattern, (tptr (Tstruct _Pat noattr))) ::
                (_action, (Tstruct _ActionRef noattr)) :: nil);
  fn_vars := ((_action, (Tstruct _ActionRef noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Sassign (Evar _action (Tstruct _ActionRef noattr))
  (Etempvar _action (Tstruct _ActionRef noattr)))
|}.

Definition f_init_table := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr (Tstruct _Table noattr))) ::
                (_num_keys, tint) :: (_size, tint) :: (_args_lub, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
Sskip
|}.

Definition f_add_entry := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr (Tstruct _Table noattr))) ::
                (_entry, (tptr (Tstruct _Entry noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
Sskip
|}.

Definition f_table_match := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _ActionRef noattr))) ::
                (_table, (tptr (Tstruct _Table noattr))) ::
                (_keys, (tptr (Tstruct _BitVec noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
Sskip
|}.

Definition composites : list composite_definition :=
(Composite __585 Struct
   ((__mp_alloc, tint) :: (__mp_size, tint) :: (__mp_d, (tptr tulong)) ::
    nil)
   noattr ::
 Composite _BitVec Struct
   ((_is_signed, tint) :: (_width, tint) ::
    (_value, (tarray (Tstruct __585 noattr) 1)) :: nil)
   noattr ::
 Composite _Pat Struct
   ((_mask, (Tstruct _BitVec noattr)) :: (_val, (Tstruct _BitVec noattr)) ::
    nil)
   noattr ::
 Composite _ActionRef Struct
   ((_action, tint) :: (_arguments, (tptr (Tstruct _BitVec noattr))) ::
    (_num_args, tint) :: nil)
   noattr ::
 Composite _Entry Struct
   ((_pattern, (tptr (Tstruct _Pat noattr))) ::
    (_action_ref, (Tstruct _ActionRef noattr)) :: nil)
   noattr ::
 Composite _Table Struct
   ((_num_keys, tint) :: (_num_entries, tint) :: (_capacity, tint) ::
    (_entries, (tptr (Tstruct _Entry noattr))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_1, Gvar v___stringlit_1) ::
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
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
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
     (Tcons (tptr (Tstruct __585 noattr))
       (Tcons (tptr (Tstruct __585 noattr))
         (Tcons (tptr (Tstruct __585 noattr)) Tnil))) tvoid cc_default)) ::
 (___gmpz_and,
   Gfun(External (EF_external "__gmpz_and"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __585 noattr))
       (Tcons (tptr (Tstruct __585 noattr))
         (Tcons (tptr (Tstruct __585 noattr)) Tnil))) tvoid cc_default)) ::
 (___gmpz_cdiv_q,
   Gfun(External (EF_external "__gmpz_cdiv_q"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __585 noattr))
       (Tcons (tptr (Tstruct __585 noattr))
         (Tcons (tptr (Tstruct __585 noattr)) Tnil))) tvoid cc_default)) ::
 (___gmpz_clear,
   Gfun(External (EF_external "__gmpz_clear"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __585 noattr)) Tnil) tvoid cc_default)) ::
 (___gmpz_cmp,
   Gfun(External (EF_external "__gmpz_cmp"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tint
                     cc_default))
     (Tcons (tptr (Tstruct __585 noattr))
       (Tcons (tptr (Tstruct __585 noattr)) Tnil)) tint cc_default)) ::
 (___gmpz_cmp_d,
   Gfun(External (EF_external "__gmpz_cmp_d"
                   (mksignature (AST.Tlong :: AST.Tfloat :: nil) AST.Tint
                     cc_default))
     (Tcons (tptr (Tstruct __585 noattr)) (Tcons tdouble Tnil)) tint
     cc_default)) ::
 (___gmpz_fdiv_q_2exp,
   Gfun(External (EF_external "__gmpz_fdiv_q_2exp"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __585 noattr))
       (Tcons (tptr (Tstruct __585 noattr)) (Tcons tulong Tnil))) tvoid
     cc_default)) ::
 (___gmpz_fdiv_r_ui,
   Gfun(External (EF_external "__gmpz_fdiv_r_ui"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tlong cc_default))
     (Tcons (tptr (Tstruct __585 noattr))
       (Tcons (tptr (Tstruct __585 noattr)) (Tcons tulong Tnil))) tulong
     cc_default)) ::
 (___gmpz_init,
   Gfun(External (EF_external "__gmpz_init"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __585 noattr)) Tnil) tvoid cc_default)) ::
 (___gmpz_ior,
   Gfun(External (EF_external "__gmpz_ior"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __585 noattr))
       (Tcons (tptr (Tstruct __585 noattr))
         (Tcons (tptr (Tstruct __585 noattr)) Tnil))) tvoid cc_default)) ::
 (___gmpz_mod,
   Gfun(External (EF_external "__gmpz_mod"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __585 noattr))
       (Tcons (tptr (Tstruct __585 noattr))
         (Tcons (tptr (Tstruct __585 noattr)) Tnil))) tvoid cc_default)) ::
 (___gmpz_mul,
   Gfun(External (EF_external "__gmpz_mul"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __585 noattr))
       (Tcons (tptr (Tstruct __585 noattr))
         (Tcons (tptr (Tstruct __585 noattr)) Tnil))) tvoid cc_default)) ::
 (___gmpz_mul_2exp,
   Gfun(External (EF_external "__gmpz_mul_2exp"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __585 noattr))
       (Tcons (tptr (Tstruct __585 noattr)) (Tcons tulong Tnil))) tvoid
     cc_default)) ::
 (___gmpz_neg,
   Gfun(External (EF_external "__gmpz_neg"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct __585 noattr))
       (Tcons (tptr (Tstruct __585 noattr)) Tnil)) tvoid cc_default)) ::
 (___gmpz_set,
   Gfun(External (EF_external "__gmpz_set"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct __585 noattr))
       (Tcons (tptr (Tstruct __585 noattr)) Tnil)) tvoid cc_default)) ::
 (___gmpz_set_str,
   Gfun(External (EF_external "__gmpz_set_str"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tint :: nil)
                     AST.Tint cc_default))
     (Tcons (tptr (Tstruct __585 noattr))
       (Tcons (tptr tschar) (Tcons tint Tnil))) tint cc_default)) ::
 (___gmpz_set_ui,
   Gfun(External (EF_external "__gmpz_set_ui"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct __585 noattr)) (Tcons tulong Tnil)) tvoid
     cc_default)) ::
 (___gmpz_sub,
   Gfun(External (EF_external "__gmpz_sub"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __585 noattr))
       (Tcons (tptr (Tstruct __585 noattr))
         (Tcons (tptr (Tstruct __585 noattr)) Tnil))) tvoid cc_default)) ::
 (___gmpz_tdiv_q_2exp,
   Gfun(External (EF_external "__gmpz_tdiv_q_2exp"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __585 noattr))
       (Tcons (tptr (Tstruct __585 noattr)) (Tcons tulong Tnil))) tvoid
     cc_default)) ::
 (___gmpz_xor,
   Gfun(External (EF_external "__gmpz_xor"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __585 noattr))
       (Tcons (tptr (Tstruct __585 noattr))
         (Tcons (tptr (Tstruct __585 noattr)) Tnil))) tvoid cc_default)) ::
 (___assert_fail,
   Gfun(External (EF_external "__assert_fail"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tschar)
       (Tcons (tptr tschar) (Tcons tuint (Tcons (tptr tschar) Tnil)))) tvoid
     cc_default)) ::
 (_pow,
   Gfun(External (EF_external "pow"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (_reset_bitvec, Gfun(Internal f_reset_bitvec)) ::
 (___func__, Gvar v___func__) ::
 (_init_bitvec, Gfun(Internal f_init_bitvec)) ::
 (_eval_uminus, Gfun(Internal f_eval_uminus)) ::
 (_eval_sat_add_sub, Gfun(Internal f_eval_sat_add_sub)) ::
 (_init_interp_binary_op, Gfun(Internal f_init_interp_binary_op)) ::
 (_interp_bplus, Gfun(Internal f_interp_bplus)) ::
 (_interp_bplus_sat, Gfun(Internal f_interp_bplus_sat)) ::
 (_interp_bminus, Gfun(Internal f_interp_bminus)) ::
 (_interp_bminus_sat, Gfun(Internal f_interp_bminus_sat)) ::
 (_interp_bmult, Gfun(Internal f_interp_bmult)) ::
 (_interp_bdiv, Gfun(Internal f_interp_bdiv)) ::
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
 (_interp_band, Gfun(Internal f_interp_band)) ::
 (_interp_bor, Gfun(Internal f_interp_bor)) ::
 (_init_pattern, Gfun(Internal f_init_pattern)) ::
 (_init_action, Gfun(Internal f_init_action)) ::
 (_init_Entry, Gfun(Internal f_init_Entry)) ::
 (_init_table, Gfun(Internal f_init_table)) ::
 (_add_entry, Gfun(Internal f_add_entry)) ::
 (_table_match, Gfun(Internal f_table_match)) :: nil).

Definition public_idents : list ident :=
(_table_match :: _add_entry :: _init_table :: _init_Entry :: _init_action ::
 _init_pattern :: _interp_bor :: _interp_band :: _interp_bitwise_or ::
 _interp_bitwise_xor :: _interp_bitwise_and :: _interp_bne :: _interp_beq ::
 _interp_bgt :: _interp_blt :: _interp_bge :: _interp_ble :: _interp_bshr ::
 _interp_bshl :: _interp_bmod :: _interp_bdiv :: _interp_bmult ::
 _interp_bminus_sat :: _interp_bminus :: _interp_bplus_sat ::
 _interp_bplus :: _init_interp_binary_op :: _eval_sat_add_sub ::
 _eval_uminus :: _init_bitvec :: _reset_bitvec :: _pow :: ___assert_fail ::
 ___gmpz_xor :: ___gmpz_tdiv_q_2exp :: ___gmpz_sub :: ___gmpz_set_ui ::
 ___gmpz_set_str :: ___gmpz_set :: ___gmpz_neg :: ___gmpz_mul_2exp ::
 ___gmpz_mul :: ___gmpz_mod :: ___gmpz_ior :: ___gmpz_init ::
 ___gmpz_fdiv_r_ui :: ___gmpz_fdiv_q_2exp :: ___gmpz_cmp_d :: ___gmpz_cmp ::
 ___gmpz_clear :: ___gmpz_cdiv_q :: ___gmpz_and :: ___gmpz_add :: _malloc ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___builtin_expect :: ___builtin_unreachable ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


