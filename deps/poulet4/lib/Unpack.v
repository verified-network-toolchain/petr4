Require Import Coq.Numbers.BinNums.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.

Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.State.

Require Import Poulet4.Syntax.
Require Import Poulet4.Environment.Environment.
Require Import Poulet4.Typed.

Open Scope string_scope.
Open Scope type_scope.

Section Unpack.
  Context (bit: Type).
  Context (tags_t: Type).
  Notation env_monad := (env_monad tags_t bit).
  Notation Value := (@Value tags_t bit).
  Notation ValueBase := (@ValueBase tags_t).
  Notation ValueLoc := (@ValueLoc tags_t).
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).
  Notation P4Parameter := (@Typed.P4Parameter tags_t).

  Definition unpack_bool (wrapped: env_monad Value) : env_monad bit :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseBool b) => mret b
    | _ => state_fail (TypeError "Cannot unpack value as boolean.")
    end.

  (* TODO: unpack_fixed_bit, unpack_var_bit; dependent types make things hard here *)

  Definition unpack_fixed_bits (wrapped: env_monad Value) : env_monad (list bit) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseBit n) => state_return n
    | _ => state_fail (TypeError "Cannot unpack value as fixed-with bits.")
    end.

  Definition unpack_var_bits (wrapped: env_monad Value) : env_monad (N * list bit) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseVarbit m n) => state_return (m, n)
    | _ => state_fail (TypeError "Cannot unpack value as variable-width bits.")
    end.

  Definition unpack_fixed_int (wrapped: env_monad Value) : env_monad (list bit) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseInt n) => state_return n
    | _ => state_fail (TypeError "Cannot unpack value as fixed-width integer.")
    end.

  Definition unpack_inf_int (wrapped: env_monad Value) : env_monad Z :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseInteger n) => mret n
    | _ => state_fail (TypeError "Cannot unpack value as variable-width integer.")
    end.

  Definition unpack_string (wrapped: env_monad Value) : env_monad string :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseString s) => mret s.(P4String.str)
    | _ => state_fail (TypeError "Cannot unpack value as string")
    end.

  Definition unpack_array (wrapped: env_monad Value) : env_monad (list ValueBase) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseTuple vals) => mret vals
    | _ => state_fail (TypeError "Cannot unpack value as tuple.")
    end.

  Definition unpack_error (wrapped: env_monad Value) : env_monad P4String :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseError e) => mret e
    | _ => state_fail (TypeError "Cannot unpack value as error.")
    end.

  Definition unpack_record (wrapped: env_monad Value) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseRecord fs) => mret fs
    | _ => state_fail (TypeError "Cannot unpack value as record.")
    end.

  Definition unpack_func (wrapped: env_monad Value) : env_monad (list P4Parameter * ValueFunctionImplementation) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValObj _ (ValObjFun params impl) => mret (params, impl)
    | _ => state_fail (TypeError "Cannot unpack value as function")
    end.

  Definition unpack_extern_obj (wrapped: env_monad Value) : env_monad (list (P4String * list P4Parameter)) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValCons _ (ValConsExternObj e) => mret e
    | _ => state_fail (TypeError "Cannot unpack value as extern object.")
    end.

  Definition unpack_packet (wrapped: env_monad Value) : env_monad (list bool) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValObj _ (ValObjPacket e) => mret e
    | _ => state_fail (TypeError "Cannot unpack value as packet.")
    end.

  Definition unpack_header (wrapped: env_monad Value) : env_monad (list (P4String * ValueBase) * bit) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseHeader h v) => mret (h, v)
    | _ => state_fail (TypeError "Cannot unpack value as header.")
    end.

  Definition unpack_header_stack (wrapped: env_monad Value) : env_monad (list ValueBase * N * N) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase _ (ValBaseStack hdrs size next) => mret (hdrs, size, next)
    | _ => state_fail (TypeError "Cannot unpack value as header stack.")
    end.

End Unpack.
