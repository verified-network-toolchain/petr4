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

Definition _BitVec : ident := $"BitVec".
Definition __585 : ident := $"_585".
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
Definition ___gmpz_set_ui : ident := $"__gmpz_set_ui".
Definition ___gmpz_sub : ident := $"__gmpz_sub".
Definition ___gmpz_tdiv_q_2exp : ident := $"__gmpz_tdiv_q_2exp".
Definition ___gmpz_xor : ident := $"__gmpz_xor".
Definition __mp_alloc : ident := $"_mp_alloc".
Definition __mp_d : ident := $"_mp_d".
Definition __mp_size : ident := $"_mp_size".
Definition __res : ident := $"_res".
Definition __res__1 : ident := $"_res__1".
Definition _dst : ident := $"dst".
Definition _dst_value : ident := $"dst_value".
Definition _eval_and : ident := $"eval_and".
Definition _eval_bitand : ident := $"eval_bitand".
Definition _eval_bitor : ident := $"eval_bitor".
Definition _eval_bitxor : ident := $"eval_bitxor".
Definition _eval_div : ident := $"eval_div".
Definition _eval_eq : ident := $"eval_eq".
Definition _eval_ge : ident := $"eval_ge".
Definition _eval_gt : ident := $"eval_gt".
Definition _eval_le : ident := $"eval_le".
Definition _eval_lt : ident := $"eval_lt".
Definition _eval_minus : ident := $"eval_minus".
Definition _eval_minus_sat : ident := $"eval_minus_sat".
Definition _eval_mod : ident := $"eval_mod".
Definition _eval_mul : ident := $"eval_mul".
Definition _eval_not_eq : ident := $"eval_not_eq".
Definition _eval_or : ident := $"eval_or".
Definition _eval_plus : ident := $"eval_plus".
Definition _eval_plus_sat : ident := $"eval_plus_sat".
Definition _eval_sat_add_sub : ident := $"eval_sat_add_sub".
Definition _eval_shl : ident := $"eval_shl".
Definition _eval_shr : ident := $"eval_shr".
Definition _eval_uminus : ident := $"eval_uminus".
Definition _init_interp_binary_op : ident := $"init_interp_binary_op".
Definition _is_add : ident := $"is_add".
Definition _is_signed : ident := $"is_signed".
Definition _l : ident := $"l".
Definition _main : ident := $"main".
Definition _op : ident := $"op".
Definition _pow : ident := $"pow".
Definition _r : ident := $"r".
Definition _reset_bitvec : ident := $"reset_bitvec".
Definition _v : ident := $"v".
Definition _value : ident := $"value".
Definition _width : ident := $"width".
Definition _x : ident := $"x".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.

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
                  ((Econst_int (Int.repr 2) tint) ::
                   (Efield
                     (Ederef (Etempvar _dst (tptr (Tstruct _BitVec noattr)))
                       (Tstruct _BitVec noattr)) _width tint) :: nil))
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
                   (Ebinop Osub (Etempvar _t'1 tdouble)
                     (Econst_int (Int.repr 1) tint) tdouble) :: nil))))))))))
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

Definition f_eval_plus := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _BitVec noattr))) :: (_op, tint) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res__1, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Ssequence
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res__1 (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res__1 (Tstruct _BitVec noattr))))
      (Ssequence
        (Scall None
          (Evar ___gmpz_add (Tfunction
                              (Tcons (tptr (Tstruct __585 noattr))
                                (Tcons (tptr (Tstruct __585 noattr))
                                  (Tcons (tptr (Tstruct __585 noattr)) Tnil)))
                              tvoid cc_default))
          ((Efield (Evar _dst (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _l (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _r (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) :: nil))
        (Ssequence
          (Scall None
            (Evar ___gmpz_fdiv_r_ui (Tfunction
                                      (Tcons (tptr (Tstruct __585 noattr))
                                        (Tcons (tptr (Tstruct __585 noattr))
                                          (Tcons tulong Tnil))) tulong
                                      cc_default))
            ((Efield (Evar _dst (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __585 noattr) 1)) ::
             (Efield (Evar _dst (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __585 noattr) 1)) ::
             (Efield (Evar _dst (Tstruct _BitVec noattr)) _width tint) ::
             nil))
          (Ssequence
            (Sassign
              (Ederef (Etempvar __res (tptr (Tstruct _BitVec noattr)))
                (Tstruct _BitVec noattr))
              (Evar _dst (Tstruct _BitVec noattr)))
            (Sreturn None)))))))
|}.

Definition f_eval_plus_sat := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _BitVec noattr))) :: (_op, tint) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res__1, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Ssequence
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res__1 (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res__1 (Tstruct _BitVec noattr))))
      (Ssequence
        (Scall None
          (Evar _eval_sat_add_sub (Tfunction
                                    (Tcons (tptr (Tstruct _BitVec noattr))
                                      (Tcons (Tstruct _BitVec noattr)
                                        (Tcons (Tstruct _BitVec noattr)
                                          (Tcons tint Tnil)))) tvoid
                                    cc_default))
          ((Eaddrof (Evar _dst (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) ::
           (Evar _r (Tstruct _BitVec noattr)) ::
           (Econst_int (Int.repr 1) tint) :: nil))
        (Ssequence
          (Sassign
            (Ederef (Etempvar __res (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) (Evar _dst (Tstruct _BitVec noattr)))
          (Sreturn None))))))
|}.

Definition f_eval_minus := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _BitVec noattr))) :: (_op, tint) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res__1, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Ssequence
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res__1 (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res__1 (Tstruct _BitVec noattr))))
      (Ssequence
        (Scall None
          (Evar ___gmpz_sub (Tfunction
                              (Tcons (tptr (Tstruct __585 noattr))
                                (Tcons (tptr (Tstruct __585 noattr))
                                  (Tcons (tptr (Tstruct __585 noattr)) Tnil)))
                              tvoid cc_default))
          ((Efield (Evar _dst (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _l (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _r (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) :: nil))
        (Ssequence
          (Scall None
            (Evar ___gmpz_fdiv_r_ui (Tfunction
                                      (Tcons (tptr (Tstruct __585 noattr))
                                        (Tcons (tptr (Tstruct __585 noattr))
                                          (Tcons tulong Tnil))) tulong
                                      cc_default))
            ((Efield (Evar _dst (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __585 noattr) 1)) ::
             (Efield (Evar _dst (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __585 noattr) 1)) ::
             (Efield (Evar _dst (Tstruct _BitVec noattr)) _width tint) ::
             nil))
          (Ssequence
            (Sassign
              (Ederef (Etempvar __res (tptr (Tstruct _BitVec noattr)))
                (Tstruct _BitVec noattr))
              (Evar _dst (Tstruct _BitVec noattr)))
            (Sreturn None)))))))
|}.

Definition f_eval_minus_sat := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _BitVec noattr))) :: (_op, tint) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res__1, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Ssequence
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res__1 (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res__1 (Tstruct _BitVec noattr))))
      (Ssequence
        (Scall None
          (Evar _eval_sat_add_sub (Tfunction
                                    (Tcons (tptr (Tstruct _BitVec noattr))
                                      (Tcons (Tstruct _BitVec noattr)
                                        (Tcons (Tstruct _BitVec noattr)
                                          (Tcons tint Tnil)))) tvoid
                                    cc_default))
          ((Eaddrof (Evar _dst (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) ::
           (Evar _r (Tstruct _BitVec noattr)) ::
           (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) :: nil))
        (Ssequence
          (Sassign
            (Ederef (Etempvar __res (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) (Evar _dst (Tstruct _BitVec noattr)))
          (Sreturn None))))))
|}.

Definition f_eval_mul := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _BitVec noattr))) :: (_op, tint) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res__1, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Ssequence
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res__1 (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res__1 (Tstruct _BitVec noattr))))
      (Ssequence
        (Scall None
          (Evar ___gmpz_mul (Tfunction
                              (Tcons (tptr (Tstruct __585 noattr))
                                (Tcons (tptr (Tstruct __585 noattr))
                                  (Tcons (tptr (Tstruct __585 noattr)) Tnil)))
                              tvoid cc_default))
          ((Efield (Evar _dst (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _l (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _r (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) :: nil))
        (Ssequence
          (Scall None
            (Evar ___gmpz_fdiv_r_ui (Tfunction
                                      (Tcons (tptr (Tstruct __585 noattr))
                                        (Tcons (tptr (Tstruct __585 noattr))
                                          (Tcons tulong Tnil))) tulong
                                      cc_default))
            ((Efield (Evar _dst (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __585 noattr) 1)) ::
             (Efield (Evar _dst (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __585 noattr) 1)) ::
             (Efield (Evar _dst (Tstruct _BitVec noattr)) _width tint) ::
             nil))
          (Ssequence
            (Sassign
              (Ederef (Etempvar __res (tptr (Tstruct _BitVec noattr)))
                (Tstruct _BitVec noattr))
              (Evar _dst (Tstruct _BitVec noattr)))
            (Sreturn None)))))))
|}.

Definition f_eval_div := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _BitVec noattr))) :: (_op, tint) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res__1, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Ssequence
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res__1 (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res__1 (Tstruct _BitVec noattr))))
      (Ssequence
        (Scall None
          (Evar ___gmpz_cdiv_q (Tfunction
                                 (Tcons (tptr (Tstruct __585 noattr))
                                   (Tcons (tptr (Tstruct __585 noattr))
                                     (Tcons (tptr (Tstruct __585 noattr))
                                       Tnil))) tvoid cc_default))
          ((Efield (Evar _dst (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _l (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _r (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) :: nil))
        (Ssequence
          (Scall None
            (Evar ___gmpz_fdiv_r_ui (Tfunction
                                      (Tcons (tptr (Tstruct __585 noattr))
                                        (Tcons (tptr (Tstruct __585 noattr))
                                          (Tcons tulong Tnil))) tulong
                                      cc_default))
            ((Efield (Evar _dst (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __585 noattr) 1)) ::
             (Efield (Evar _dst (Tstruct _BitVec noattr)) _value
               (tarray (Tstruct __585 noattr) 1)) ::
             (Efield (Evar _dst (Tstruct _BitVec noattr)) _width tint) ::
             nil))
          (Ssequence
            (Sassign
              (Ederef (Etempvar __res (tptr (Tstruct _BitVec noattr)))
                (Tstruct _BitVec noattr))
              (Evar _dst (Tstruct _BitVec noattr)))
            (Sreturn None)))))))
|}.

Definition f_eval_mod := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _BitVec noattr))) :: (_op, tint) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res__1, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Ssequence
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res__1 (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res__1 (Tstruct _BitVec noattr))))
      (Ssequence
        (Scall None
          (Evar ___gmpz_mod (Tfunction
                              (Tcons (tptr (Tstruct __585 noattr))
                                (Tcons (tptr (Tstruct __585 noattr))
                                  (Tcons (tptr (Tstruct __585 noattr)) Tnil)))
                              tvoid cc_default))
          ((Efield (Evar _dst (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _l (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _r (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) :: nil))
        (Ssequence
          (Sassign
            (Ederef (Etempvar __res (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) (Evar _dst (Tstruct _BitVec noattr)))
          (Sreturn None))))))
|}.

Definition f_eval_shl := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _BitVec noattr))) :: (_op, tint) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res__1, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Ssequence
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res__1 (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res__1 (Tstruct _BitVec noattr))))
      (Ssequence
        (Scall None
          (Evar ___gmpz_mul_2exp (Tfunction
                                   (Tcons (tptr (Tstruct __585 noattr))
                                     (Tcons (tptr (Tstruct __585 noattr))
                                       (Tcons tulong Tnil))) tvoid
                                   cc_default))
          ((Efield (Evar _dst (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _l (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _r (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) :: nil))
        (Ssequence
          (Sassign
            (Ederef (Etempvar __res (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) (Evar _dst (Tstruct _BitVec noattr)))
          (Sreturn None))))))
|}.

Definition f_eval_shr := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _BitVec noattr))) :: (_op, tint) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res__1, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Ssequence
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res__1 (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res__1 (Tstruct _BitVec noattr))))
      (Sifthenelse (Efield (Evar _dst (Tstruct _BitVec noattr)) _is_signed
                     tint)
        (Scall None
          (Evar ___gmpz_fdiv_q_2exp (Tfunction
                                      (Tcons (tptr (Tstruct __585 noattr))
                                        (Tcons (tptr (Tstruct __585 noattr))
                                          (Tcons tulong Tnil))) tvoid
                                      cc_default))
          ((Efield (Evar _dst (Tstruct _BitVec noattr)) _value
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
          ((Efield (Evar _dst (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _l (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _r (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) :: nil))))))
|}.

Definition f_eval_le := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_op, tint) :: (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res, (Tstruct _BitVec noattr)) :: nil);
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
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res (Tstruct _BitVec noattr))))
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
            (Sreturn (Some (Econst_int (Int.repr 1) tint)))
            Sskip))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_eval_ge := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_op, tint) :: (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res, (Tstruct _BitVec noattr)) :: nil);
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
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res (Tstruct _BitVec noattr))))
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
            (Sreturn (Some (Econst_int (Int.repr 1) tint)))
            Sskip))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_eval_lt := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_op, tint) :: (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res, (Tstruct _BitVec noattr)) :: nil);
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
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res (Tstruct _BitVec noattr))))
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
            (Sreturn (Some (Econst_int (Int.repr 1) tint)))
            Sskip))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_eval_gt := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_op, tint) :: (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res, (Tstruct _BitVec noattr)) :: nil);
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
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res (Tstruct _BitVec noattr))))
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
            (Sreturn (Some (Econst_int (Int.repr 1) tint)))
            Sskip))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_eval_eq := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_op, tint) :: (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res, (Tstruct _BitVec noattr)) :: nil);
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
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res (Tstruct _BitVec noattr))))
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
            (Sreturn (Some (Econst_int (Int.repr 1) tint)))
            Sskip))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_eval_not_eq := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_op, tint) :: (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res, (Tstruct _BitVec noattr)) :: nil);
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
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res (Tstruct _BitVec noattr))))
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
            (Sreturn (Some (Econst_int (Int.repr 1) tint)))
            Sskip))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_eval_bitand := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _BitVec noattr))) :: (_op, tint) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res__1, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Ssequence
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res__1 (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res__1 (Tstruct _BitVec noattr))))
      (Ssequence
        (Scall None
          (Evar ___gmpz_and (Tfunction
                              (Tcons (tptr (Tstruct __585 noattr))
                                (Tcons (tptr (Tstruct __585 noattr))
                                  (Tcons (tptr (Tstruct __585 noattr)) Tnil)))
                              tvoid cc_default))
          ((Efield (Evar _dst (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _l (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _r (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) :: nil))
        (Ssequence
          (Sassign
            (Ederef (Etempvar __res (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) (Evar _dst (Tstruct _BitVec noattr)))
          (Sreturn None))))))
|}.

Definition f_eval_bitxor := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _BitVec noattr))) :: (_op, tint) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res__1, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Ssequence
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res__1 (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res__1 (Tstruct _BitVec noattr))))
      (Ssequence
        (Scall None
          (Evar ___gmpz_xor (Tfunction
                              (Tcons (tptr (Tstruct __585 noattr))
                                (Tcons (tptr (Tstruct __585 noattr))
                                  (Tcons (tptr (Tstruct __585 noattr)) Tnil)))
                              tvoid cc_default))
          ((Efield (Evar _dst (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _l (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _r (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) :: nil))
        (Ssequence
          (Sassign
            (Ederef (Etempvar __res (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) (Evar _dst (Tstruct _BitVec noattr)))
          (Sreturn None))))))
|}.

Definition f_eval_bitor := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _BitVec noattr))) :: (_op, tint) ::
                (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res__1, (Tstruct _BitVec noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _l (Tstruct _BitVec noattr))
    (Etempvar _l (Tstruct _BitVec noattr)))
  (Ssequence
    (Sassign (Evar _r (Tstruct _BitVec noattr))
      (Etempvar _r (Tstruct _BitVec noattr)))
    (Ssequence
      (Ssequence
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res__1 (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res__1 (Tstruct _BitVec noattr))))
      (Ssequence
        (Scall None
          (Evar ___gmpz_ior (Tfunction
                              (Tcons (tptr (Tstruct __585 noattr))
                                (Tcons (tptr (Tstruct __585 noattr))
                                  (Tcons (tptr (Tstruct __585 noattr)) Tnil)))
                              tvoid cc_default))
          ((Efield (Evar _dst (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _l (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) ::
           (Efield (Evar _r (Tstruct _BitVec noattr)) _value
             (tarray (Tstruct __585 noattr) 1)) :: nil))
        (Ssequence
          (Sassign
            (Ederef (Etempvar __res (tptr (Tstruct _BitVec noattr)))
              (Tstruct _BitVec noattr)) (Evar _dst (Tstruct _BitVec noattr)))
          (Sreturn None))))))
|}.

Definition f_eval_and := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_op, tint) :: (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res, (Tstruct _BitVec noattr)) :: nil);
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
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res (Tstruct _BitVec noattr))))
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
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_eval_or := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_op, tint) :: (_l, (Tstruct _BitVec noattr)) ::
                (_r, (Tstruct _BitVec noattr)) :: nil);
  fn_vars := ((_l, (Tstruct _BitVec noattr)) ::
              (_r, (Tstruct _BitVec noattr)) ::
              (_dst, (Tstruct _BitVec noattr)) ::
              (__res, (Tstruct _BitVec noattr)) :: nil);
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
        (Scall None
          (Evar _init_interp_binary_op (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BitVec noattr))
                                           (Tcons (Tstruct _BitVec noattr)
                                             Tnil)) tvoid
                                         {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
          ((Eaddrof (Evar __res (Tstruct _BitVec noattr))
             (tptr (Tstruct _BitVec noattr))) ::
           (Evar _l (Tstruct _BitVec noattr)) :: nil))
        (Sassign (Evar _dst (Tstruct _BitVec noattr))
          (Evar __res (Tstruct _BitVec noattr))))
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
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition composites : list composite_definition :=
(Composite __585 Struct
   ((__mp_alloc, tint) :: (__mp_size, tint) :: (__mp_d, (tptr tulong)) ::
    nil)
   noattr ::
 Composite _BitVec Struct
   ((_is_signed, tint) :: (_width, tint) ::
    (_value, (tarray (Tstruct __585 noattr) 1)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
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
 (_pow,
   Gfun(External (EF_external "pow"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (_reset_bitvec, Gfun(Internal f_reset_bitvec)) ::
 (_eval_uminus, Gfun(Internal f_eval_uminus)) ::
 (_eval_sat_add_sub, Gfun(Internal f_eval_sat_add_sub)) ::
 (_init_interp_binary_op, Gfun(Internal f_init_interp_binary_op)) ::
 (_eval_plus, Gfun(Internal f_eval_plus)) ::
 (_eval_plus_sat, Gfun(Internal f_eval_plus_sat)) ::
 (_eval_minus, Gfun(Internal f_eval_minus)) ::
 (_eval_minus_sat, Gfun(Internal f_eval_minus_sat)) ::
 (_eval_mul, Gfun(Internal f_eval_mul)) ::
 (_eval_div, Gfun(Internal f_eval_div)) ::
 (_eval_mod, Gfun(Internal f_eval_mod)) ::
 (_eval_shl, Gfun(Internal f_eval_shl)) ::
 (_eval_shr, Gfun(Internal f_eval_shr)) ::
 (_eval_le, Gfun(Internal f_eval_le)) ::
 (_eval_ge, Gfun(Internal f_eval_ge)) ::
 (_eval_lt, Gfun(Internal f_eval_lt)) ::
 (_eval_gt, Gfun(Internal f_eval_gt)) ::
 (_eval_eq, Gfun(Internal f_eval_eq)) ::
 (_eval_not_eq, Gfun(Internal f_eval_not_eq)) ::
 (_eval_bitand, Gfun(Internal f_eval_bitand)) ::
 (_eval_bitxor, Gfun(Internal f_eval_bitxor)) ::
 (_eval_bitor, Gfun(Internal f_eval_bitor)) ::
 (_eval_and, Gfun(Internal f_eval_and)) ::
 (_eval_or, Gfun(Internal f_eval_or)) :: nil).

Definition public_idents : list ident :=
(_eval_or :: _eval_and :: _eval_bitor :: _eval_bitxor :: _eval_bitand ::
 _eval_not_eq :: _eval_eq :: _eval_gt :: _eval_lt :: _eval_ge :: _eval_le ::
 _eval_shr :: _eval_shl :: _eval_mod :: _eval_div :: _eval_mul ::
 _eval_minus_sat :: _eval_minus :: _eval_plus_sat :: _eval_plus ::
 _init_interp_binary_op :: _eval_sat_add_sub :: _eval_uminus ::
 _reset_bitvec :: _pow :: ___gmpz_xor :: ___gmpz_tdiv_q_2exp ::
 ___gmpz_sub :: ___gmpz_set_ui :: ___gmpz_neg :: ___gmpz_mul_2exp ::
 ___gmpz_mul :: ___gmpz_mod :: ___gmpz_ior :: ___gmpz_init ::
 ___gmpz_fdiv_r_ui :: ___gmpz_fdiv_q_2exp :: ___gmpz_cmp_d :: ___gmpz_cmp ::
 ___gmpz_clear :: ___gmpz_cdiv_q :: ___gmpz_and :: ___gmpz_add ::
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


