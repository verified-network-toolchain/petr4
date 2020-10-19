Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Strings.String.

Require Import Monads.Monad.
Require Import Monads.State.

Require Import Value.
Require Import Environment.

Definition unpack_bool (wrapped: env_monad value) : env_monad bool :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValBool b => mret b
  | _ => state_fail Internal
  end.

(* TODO: unpack_fixed_bit, unpack_var_bit; dependent types make things hard here *)

Definition unpack_fixed_int (wrapped: env_monad value) : env_monad (nat * Z) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValFixedInt w n => mret (w, n)
  | _ => state_fail Internal
  end.

Definition unpack_inf_int (wrapped: env_monad value) : env_monad Z :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValInfInt n => mret n
  | _ => state_fail Internal
  end.

Definition unpack_string (wrapped: env_monad value) : env_monad string :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValString s => mret s
  | _ => state_fail Internal
  end.

Definition unpack_array (wrapped: env_monad value) : env_monad (list value) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValArray a => mret a
  | _ => state_fail Internal
  end.

Definition unpack_error (wrapped: env_monad value) : env_monad string :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValError e => mret e
  | _ => state_fail Internal
  end.

Definition unpack_record (wrapped: env_monad value) : env_monad (MStr.Raw.t value) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValRecord fs => mret fs
  | _ => state_fail Internal
  end.

Definition unpack_builtin_func (wrapped: env_monad value) : env_monad (string * lvalue) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValBuiltinFunc name obj => mret (name, obj)
  | _ => state_fail Internal
  end.

Definition unpack_extern_func (wrapped: env_monad value) : env_monad (string * lvalue) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValExternFunc name obj => mret (name, obj)
  | _ => state_fail Internal
  end.

Definition unpack_extern_obj (wrapped: env_monad value) : env_monad extern :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValExternObj e => mret e
  | _ => state_fail Internal
  end.

Definition unpack_header (wrapped: env_monad value) : env_monad header :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValHeader h => mret h
  | _ => state_fail Internal
  end.

Definition unpack_header_stack (wrapped: env_monad value) : env_monad (nat * nat * (list header)) :=
  let* unwrapped := wrapped in
  match unwrapped with
  | ValHeaderStack s n hdrs => mret (s, n, hdrs)
  | _ => state_fail Internal
  end.
