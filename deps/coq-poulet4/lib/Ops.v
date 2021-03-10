Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Syntax.
Require Import Typed.

Module Ops.
  Section Operations.
  Context {tags_t: Type}.

  Notation Val := (@ValueBase tags_t).
  Definition eval_unary_op (op : OpUni) (v : Val) : option Val.
  Admitted.
    (* match op, v with
    | (Not, ValBaseBool b) => ValBaseBool (negb b)
    | (BitNot, ValBaseBit w v) => ValBaseBit w (BitArith.neg w n)
    | (UMinus, ValBaseBit w v) => ValBaseBit w (BitArith.neg w n)
    | (UMinus, ValBaseInt w v) => 
    | (UMinus, ValBaseInteger v) => ValBaseInteger (- v)%Z
    | _ => None
    end. *)

  Definition eval_binary_op (op: OpBin) (v1 : Val) (v2 : Val) : option Val.
  Admitted.

  Definition eval_cast (newtyp : @P4Type tags_t) (oldv : Val) : option Val.
  Admitted.
  
  
  End Operations.
End Ops.
