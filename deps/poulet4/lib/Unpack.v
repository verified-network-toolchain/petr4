Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Bool.Bvector.
Require Import Coq.Strings.String.

Require Import Monads.Monad.
Require Import Monads.State.

Require Import Syntax.
Require Import Environment.

Definition unpack_bool (wrapped: env_monad Value_value) : env_monad bool :=
  let* unwrapped := wrapped in
  match unwrapped with
  | Val_Bool b => mret b
  | _ => state_fail Internal
  end.

(* TODO: unpack_fixed_bit, unpack_var_bit; dependent types make things hard here *)
Definition unpack_fixed_int (wrapped: env_monad Value_value) : env_monad {width:nat & Bvector width} :=
  let* unwrapped := wrapped in
  match unwrapped with
  | Val_Int w n => mret (existT _ w n)
  | _ => state_fail Internal
  end.

Definition unpack_inf_int (wrapped: env_monad Value_value) : env_monad Z :=
  let* unwrapped := wrapped in
  match unwrapped with
  | Val_Integer n => mret n
  | _ => state_fail Internal
  end.

Definition unpack_string (wrapped: env_monad Value_value) : env_monad string :=
  let* unwrapped := wrapped in
  match unwrapped with
  | Val_String s => mret s
  | _ => state_fail Internal
  end.

Definition unpack_array (wrapped: env_monad Value_value) : env_monad (list Value_value) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | Val_Tuple vals => mret vals
  | _ => state_fail Internal
  end.

Definition unpack_error (wrapped: env_monad Value_value) : env_monad string :=
  let* unwrapped := wrapped in
  match unwrapped with
  | Val_Error e => mret e
  | _ => state_fail Internal
  end.

Definition unpack_record (wrapped: env_monad Value_value) : env_monad (MStr.Raw.t Value_value) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | Val_Record fs => mret fs
  | _ => state_fail Internal
  end.

Definition unpack_builtin_func (wrapped: env_monad Value_value) : env_monad (string * Value_lvalue) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | Val_BuiltinFun name obj => mret (name, obj)
  | _ => state_fail Internal
  end.

Definition unpack_extern_func (wrapped: env_monad Value_value) : env_monad (string * option (Value_loc * string) * list Typed.P4Parameter) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | Val_ExternFun name obj params => mret (name, obj, params)
  | _ => state_fail Internal
  end.

Definition unpack_extern_obj (wrapped: env_monad Value_value) : env_monad (list (string * list Typed.P4Parameter)) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | Val_ExternObj e => mret e
  | _ => state_fail Internal
  end.

Definition unpack_header (wrapped: env_monad Value_value) : env_monad (list (string * Value_value) * bool) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | Val_Header h v => mret (h, v)
  | _ => state_fail Internal
  end.

Definition unpack_header_stack (wrapped: env_monad Value_value) : env_monad (list Value_value * nat * nat) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | Val_Stack hdrs size next => mret (hdrs, size, next)
  | _ => state_fail Internal
  end.
