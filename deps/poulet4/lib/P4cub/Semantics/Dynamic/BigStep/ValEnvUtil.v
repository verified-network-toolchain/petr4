Require Import Coq.NArith.BinNat Coq.ZArith.BinInt
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Value
        Poulet4.P4cub.Semantics.Climate Poulet4.Utils.P4Arith
        Poulet4.P4cub.Semantics.Dynamic.BigStep.ExprUtil.
Import String Val.ValueNotations Val.LValueNotations.

Local Open Scope value_scope.
Local Open Scope lvalue_scope.

(** Environments for
    evaluation are De Bruijn lists of values [Val.v].
    Lookup is done via l-values [Val.lv]. *)

(** Lookup an lvalue. *)
Fixpoint lv_lookup (ϵ : list Val.v) (lv : Val.lv) : option Val.v :=
  match lv with
  | Val.Var x => nth_error ϵ x
  | Val.Slice hi lo lv => lv_lookup ϵ lv >>= eval_slice hi lo
  | lv DOT x =>
      let* v := lv_lookup ϵ lv in
      match v with
      | Val.Lists
          (Expr.lists_struct
          | Expr.lists_header _) vs => nth_error vs x
      | _ => None
      end
  | Val.Index n lv =>
      let* v := lv_lookup ϵ lv in
      match v with
      | Val.Lists (Expr.lists_array _) vs => nth_error vs $ N.to_nat n
      | _ => None
      end
  end.

(** Updating an lvalue in an environment. *)
Fixpoint lv_update
         (lv : Val.lv) (v : Val.v)
         (ϵ : list Val.v) : list Val.v :=
  match lv with
  | Val.Var x => nth_update x v ϵ
  | Val.Slice hi lo lv =>
      match v, lv_lookup ϵ lv with
      | (_ VW n | _ VS n), Some (w VW _) =>
          let rhs := N.shiftl (Z.to_N n) w in
          let mask :=
            Z.to_N
              (-1 - (Z.of_N (N.lxor
                               (2 ^ (Npos hi + 1) - 1)
                               (2 ^ (Npos lo - 1))))) in
          let new := Z.lxor (Z.land n (Z.of_N mask)) (Z.of_N rhs) in
          lv_update lv (w VW new) ϵ
      | _, _ => ϵ
      end
  | lv DOT x =>
    match lv_lookup ϵ lv with
    | Some
        (Val.Lists
           ((Expr.lists_struct
            | Expr.lists_header _) as ls) vs)
      => lv_update lv (Val.Lists ls $ nth_update x v vs) ϵ
    | _ => ϵ
    end
  | Val.Index n lv =>
      match lv_lookup ϵ lv with
      | Some
          (Val.Lists
             (Expr.lists_array _ as ls) vs)
        => lv_update lv (Val.Lists ls $ nth_update (N.to_nat n) v vs) ϵ
      | _ => ϵ
      end
  end.

(** Create a new environment
    from a closure environment where
    values of args are substituted
    into the function parameters. *)
Definition copy_in
           (argsv : Val.argsv)
           (ϵcall : list Val.v) : option (list Val.v) :=
  argsv
    ▷ map (fun arg =>
             match arg with
             | PAIn v     => Some v
             | PAOut lv
             | PAInOut lv => lv_lookup ϵcall lv
             end)
    ▷ sequence.

(** Update call-site environment with
    out variables from function call evaluation. *)

Definition copy_out
           (argsv : Val.argsv)
           (ϵ_func : list Val.v) (ϵ_call : list Val.v) : list Val.v :=
  fold_right
    (fun arg ϵ_call =>
       match arg with
       | PAIn _ => ϵ_call
       | PAOut lv
       | PAInOut lv
         => match lv_lookup ϵ_func lv with
           | None   => ϵ_call
           | Some v => lv_update lv v ϵ_call
           end
       end) ϵ_call argsv.

Local Close Scope value_scope.
Local Close Scope lvalue_scope.
