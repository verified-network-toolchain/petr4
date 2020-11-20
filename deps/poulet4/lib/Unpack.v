Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Bool.Bvector.
Require Import Coq.Strings.String.

Require Import Monads.Monad.
Require Import Monads.State.

Require Import Syntax.
Require Import Environment.

Section Unpack.
  Context (tags_t: Type).

  Definition unpack_bool (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t bool :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBool _ b => mret b
    | _ => state_fail Internal
    end.

  (* TODO: unpack_fixed_bit, unpack_var_bit; dependent types make things hard here *)
  Definition unpack_fixed_int (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t {width:nat & Bvector width} :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValInt _ w n => mret (existT _ w n)
    | _ => state_fail Internal
    end.

  Definition unpack_inf_int (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t Z :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValInteger _ n => mret n
    | _ => state_fail Internal
    end.

  Definition unpack_string (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t string :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValString _ s => mret s
    | _ => state_fail Internal
    end.

  Definition unpack_array (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t (list (Value tags_t)) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValTuple _ vals => mret vals
    | _ => state_fail Internal
    end.

  Definition unpack_error (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t string :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValError _ e => mret e
    | _ => state_fail Internal
    end.

  Definition unpack_record (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t (MStr.Raw.t (Value tags_t)) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValRecord _ fs => mret fs
    | _ => state_fail Internal
    end.

  Definition unpack_builtin_func (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t (string * ValueLvalue tags_t) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBuiltinFun _ name obj => mret (name, obj)
    | _ => state_fail Internal
    end.

  Definition unpack_extern_func (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t (string * option (ValueLoc * string) * list Typed.P4Parameter) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValExternFun _ name obj params => mret (name, obj, params)
    | _ => state_fail Internal
    end.

  Definition unpack_extern_obj (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t (list (string * list Typed.P4Parameter)) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValExternObj _ e => mret e
    | _ => state_fail Internal
    end.

  Definition unpack_header (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t (list (string * (Value tags_t)) * bool) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValHeader _ h v => mret (h, v)
    | _ => state_fail Internal
    end.

  Definition unpack_header_stack (wrapped: env_monad tags_t (Value tags_t)) : env_monad tags_t (list (Value tags_t) * nat * nat) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValStack _ hdrs size next => mret (hdrs, size, next)
    | _ => state_fail Internal
    end.

End Unpack.
