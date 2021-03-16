Require Import Coq.Numbers.BinNums.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.

Require Import Monads.Monad.
Require Import Monads.State.

Require Import Syntax.
Require Import Environment.Environment.
Require Import Typed.

Open Scope string_scope.
Open Scope type_scope.

Section Unpack.
  Context (tags_t: Type).
  Notation env_monad := (env_monad tags_t).
  Notation Value := (@Value tags_t).
  Notation ValueBase := (@ValueBase tags_t).
  Notation ValueLoc := (@ValueLoc tags_t).
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).
  Notation P4Parameter := (@Typed.P4Parameter tags_t).

  Definition unpack_bool (wrapped: env_monad Value) : env_monad bool :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase (ValBaseBool b) => mret b
    | _ => state_fail (TypeError "Cannot unpack value as boolean.")
    end.

  (* TODO: unpack_fixed_bit, unpack_var_bit; dependent types make things hard here *)

  Definition unpack_fixed_bits (wrapped: env_monad Value) : env_monad (nat * Z) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase (ValBaseBit w n) => state_return (w, n)
    | _ => state_fail (TypeError "Cannot unpack value as fixed-with bits.")
    end.

  Definition unpack_var_bits (wrapped: env_monad Value) : env_monad (nat * nat * Z) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase (ValBaseVarbit m w n) => state_return (m, w, n)
    | _ => state_fail (TypeError "Cannot unpack value as variable-width bits.")
    end.

  Definition unpack_fixed_int (wrapped: env_monad Value) : env_monad (nat * Z) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase (ValBaseInt w n) => state_return (w, n)
    | _ => state_fail (TypeError "Cannot unpack value as fixed-width integer.")
    end.

  Definition unpack_inf_int (wrapped: env_monad Value) : env_monad Z :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase (ValBaseInteger n) => mret n
    | _ => state_fail (TypeError "Cannot unpack value as variable-width integer.")
    end.

  Definition unpack_string (wrapped: env_monad Value) : env_monad string :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase (ValBaseString s) => mret s.(P4String.str)
    | _ => state_fail (TypeError "Cannot unpack value as string")
    end.

  Definition unpack_array (wrapped: env_monad Value) : env_monad (list ValueBase) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase (ValBaseTuple vals) => mret vals
    | _ => state_fail (TypeError "Cannot unpack value as tuple.")
    end.

  Definition unpack_error (wrapped: env_monad Value) : env_monad P4String :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase (ValBaseError e) => mret e
    | _ => state_fail (TypeError "Cannot unpack value as error.")
    end.

  Definition unpack_record (wrapped: env_monad Value) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase (ValBaseRecord fs) => mret fs
    | _ => state_fail (TypeError "Cannot unpack value as record.")
    end.

  Definition unpack_func (wrapped: env_monad Value) : env_monad (list P4Parameter * ValueFunctionImplementation) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValObj (ValObjFun params impl) => mret (params, impl)
    | _ => state_fail (TypeError "Cannot unpack value as function")
    end.

  Definition unpack_extern_obj (wrapped: env_monad Value) : env_monad (list (P4String * list P4Parameter)) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValCons (ValConsExternObj e) => mret e
    | _ => state_fail (TypeError "Cannot unpack value as extern object.")
    end.

  Definition unpack_packet (wrapped: env_monad Value) : env_monad (list bool) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValObj (ValObjPacket e) => mret e
    | _ => state_fail (TypeError "Cannot unpack value as packet.")
    end.

  Definition unpack_header (wrapped: env_monad Value) : env_monad (list (P4String * ValueBase) * bool) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase (ValBaseHeader h v) => mret (h, v)
    | _ => state_fail (TypeError "Cannot unpack value as header.")
    end.

  Definition unpack_header_stack (wrapped: env_monad Value) : env_monad (list ValueBase * nat * nat) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase (ValBaseStack hdrs size next)  => mret (hdrs, size, next)
    | _ => state_fail (TypeError "Cannot unpack value as header stack.")
    end.

  Definition unpack_set (wrapped: env_monad Value) : env_monad (ValueSet) :=
    let* unwrapped := wrapped in
    match unwrapped with
    | ValBase (ValBaseSet s) => mret s
    | _ => state_fail (TypeError "Cannot unpack value as set.")
    end.

End Unpack.
