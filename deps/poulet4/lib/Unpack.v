Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Bool.Bvector.

Require Import Monads.Monad.
Require Import Monads.State.

Require Import CamlString.
Require Import Syntax.
Require Import Environment.

Section Unpack.
  Context (tags_t: Type).

  Definition unpack_bool (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t bool :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseBool _ b) => mret b
    | _ => state_fail Internal
    end.

  (* TODO: unpack_fixed_bit, unpack_var_bit; dependent types make things hard here *)
  Definition unpack_fixed_int (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t {width:nat & Bvector width} :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseInt _ w n) => mret (existT _ w n)
    | _ => state_fail Internal
    end.

  Definition unpack_inf_int (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t Z :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseInteger _ n) => mret n
    | _ => state_fail Internal
    end.

  Definition unpack_string (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t caml_string :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseString _ s) => mret s
    | _ => state_fail Internal
    end.

  Definition unpack_array (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t (list (ValueBase tags_t)) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseTuple _ vals) => mret vals
    | _ => state_fail Internal
    end.

  Definition unpack_error (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t caml_string :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseError _ e) => mret e
    | _ => state_fail Internal
    end.

  Definition unpack_record (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t (MStr.Raw.t nat) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseRecord _ fs) => mret fs
    | _ => state_fail Internal
    end.

  Definition unpack_builtin_func (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t (caml_string * loc) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValObj _ (ValObjBuiltinFun _ name obj) => mret (name, obj)
    | _ => state_fail Internal
    end.

  Definition unpack_extern_func (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t (caml_string * option (ValueLoc * caml_string) * list Typed.P4Parameter) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValObj _ (ValObjExternFun _ name obj params) => mret (name, obj, params)
    | _ => state_fail Internal
    end.

  Definition unpack_extern_obj (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t (list (caml_string * list Typed.P4Parameter)) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValCons _ (ValConsExternObj _ e) => mret e
    | _ => state_fail Internal
    end.

  Definition unpack_header (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t (list (caml_string * nat) * bool) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseHeader _ h v) => mret (h, v)
    | _ => state_fail Internal
    end.

  Definition unpack_header_stack (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t (list nat * nat * nat) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseStack _ hdrs size next)  => mret (hdrs, size, next)
    | _ => state_fail Internal
    end.

End Unpack.
