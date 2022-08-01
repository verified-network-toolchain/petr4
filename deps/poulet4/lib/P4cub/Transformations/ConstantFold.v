Require Import Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Semantics.Dynamic.SmallStep.Util
        Coq.ZArith.BinInt.
Import AllCubNotations.

(** Binary operation optimizations. *)
Definition optimize_bop
           (t : Expr.t) (op : Expr.bop)
           (e1 e2 : Expr.e)
  : Expr.e :=
  match op, e1, e2 with
  | `+%bop, (_ `W Z0)%expr, e
  | `+%bop, e, (_ `W Z0)%expr
  | `-%bop, e, (_ `W Z0)%expr
  | ×%bop, (_ `W 1%Z)%expr, e
  | ×%bop, e, (_ `W 1%Z)%expr
  | <<%bop, e, (_ `W Z0)%expr
  | >>%bop, e, (_ `W Z0)%expr
  | `+%bop, (_ `S Z0)%expr, e
  | `+%bop, e, (_ `S Z0)%expr
  | `-%bop, e, (_ `S Z0)%expr
  | ×%bop, (_ `S 1%Z)%expr, e
  | ×%bop, e, (_ `S 1%Z)%expr
  | <<%bop, e, (_ `S Z0)%expr
  | >>%bop, e, (_ `S Z0)%expr
  | `&&%bop, Expr.Bool true, e
  | `&&%bop, e, Expr.Bool true
  | `||%bop, Expr.Bool false, e
  | `||%bop, e, Expr.Bool false
  | ×%bop, (_ `W Z0)%expr as e, _
  | ×%bop, _, (_ `W Z0)%expr as e
  | `&&%bop, Expr.Bool false as e, _
  | `&&%bop, _, Expr.Bool false as e
  | `||%bop, Expr.Bool true as e, _
  | `||%bop, _, Expr.Bool true as e => e
  | _, _, _ =>
      match eval_bop op e1 e2 with
      | Some e' => e'
      | None     => Expr.Bop t op e1 e2
      end
  end.

(** P4cub expression constant folding. *)
Fixpoint cf_e (e : Expr.e) : Expr.e :=
  match e with
  | Expr.Bool _
  | (_ `W _)%expr
  | (_ `S _)%expr
  | Expr.Error _
  | Expr.Var _ _ => e
  | Expr.Slice hi lo e =>
      let e' := cf_e e in
      match eval_slice hi lo e' with
      | Some e'' => e''
      | None     => Expr.Slice hi lo e'
      end
  | Expr.Cast t e =>
      let e' := cf_e e in
      match eval_cast t e' with
      | Some e'' => e''
      | None     => Expr.Cast t e'
      end
  | Expr.Uop t op e =>
      let e' := cf_e e in
      match eval_uop op e with
      | Some e'' => e''
      | None     => Expr.Uop t op e'
      end
  | Expr.Bop t op e1 e2 =>
      optimize_bop t op (cf_e e1) (cf_e e2)
  | Expr.Lists ls es => Expr.Lists ls $ map cf_e es
  | Expr.Index t e1 e2 =>
      match cf_e e1, cf_e e2 with
      | Expr.Lists _ es as e1', (_ `W n)%expr as e2'
        => match nth_error es $ Z.to_nat n with
          | Some v => v
          | None => Expr.Index t e1' e2'
          end
      | e1', e2' => Expr.Index t e1' e2'
      end
  | Expr.Member t x e =>
      match cf_e e with
      | Expr.Lists _ es as e'
        =>  match nth_error es x with
           | Some v => v
           | None => Expr.Member t x e'
           end
      | e' => Expr.Member t x e'
      end
  end.
