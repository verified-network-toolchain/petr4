Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Bool.Bvector.
Require Import Coq.Strings.String.

Require Import Monads.Monad.
Require Import Monads.State.

Require Import Syntax.
Require Import Environment.

Definition unpack_bool (wrapped: env_monad Value) : env_monad bool :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValBase (ValBaseBool b) => mret b
  | _ => state_fail Internal
  end.

(* TODO: unpack_fixed_bit, unpack_var_bit; dependent types make things hard here *)
Definition unpack_fixed_int (wrapped: env_monad Value) : env_monad {width:nat & Bvector width} :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValBase (ValBaseInt w n) => mret (existT _ w n)
  | _ => state_fail Internal
  end.

Definition unpack_inf_int (wrapped: env_monad Value) : env_monad Z :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValBase (ValBaseInteger n) => mret n
  | _ => state_fail Internal
  end.

Definition unpack_string (wrapped: env_monad Value) : env_monad string :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValBase (ValBaseString s) => mret s
  | _ => state_fail Internal
  end.

Definition unpack_array (wrapped: env_monad Value) : env_monad (list ValueBase) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValBase (ValBaseTuple vals) => mret vals
  | _ => state_fail Internal
  end.

Definition unpack_error (wrapped: env_monad Value) : env_monad string :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValBase (ValBaseError e) => mret e
  | _ => state_fail Internal
  end.

Definition unpack_record (wrapped: env_monad Value) : env_monad (MStr.Raw.t ValueBase) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValBase (ValBaseRecord fs) => mret fs
  | _ => state_fail Internal
  end.

Definition unpack_builtin_func (wrapped: env_monad Value) : env_monad (string * ValueLvalue) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValObj (ValObjBuiltinFun name obj) => mret (name, obj)
  | _ => state_fail Internal
  end.

Definition unpack_extern_func (wrapped: env_monad Value) : env_monad (string * option (ValueLoc * string) * list Typed.P4Parameter) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValObj (ValObjExternFun name obj params) => mret (name, obj, params)
  | _ => state_fail Internal
  end.

Definition unpack_extern_obj (wrapped: env_monad Value) : env_monad (list (string * list Typed.P4Parameter)) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValCons (ValConsExternObj e) => mret e
  | _ => state_fail Internal
  end.

Definition unpack_header (wrapped: env_monad Value) : env_monad (list (string * ValueBase) * bool) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValBase (ValBaseHeader h v) => mret (h, v)
  | _ => state_fail Internal
  end.

Definition unpack_header_stack (wrapped: env_monad Value) : env_monad (list ValueBase * nat * nat) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValBase (ValBaseStack hdrs size next) => mret (hdrs, size, next)
  | _ => state_fail Internal
  end.
