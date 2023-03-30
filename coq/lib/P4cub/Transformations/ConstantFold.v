Require Import Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Semantics.Dynamic.SmallStep.Util
        Coq.ZArith.BinInt.

(** Binary operation optimizations. *)
Definition optimize_bin
           (t : Typ.t) (op : Bin.t)
           (e1 e2 : Exp.t)
  : Exp.t :=
  match op, e1, e2 with
  | `+%bin, (_ `W Z0)%exp, e
  | `+%bin, e, (_ `W Z0)%exp
  | `-%bin, e, (_ `W Z0)%exp
  | ×%bin, (_ `W 1%Z)%exp, e
  | ×%bin, e, (_ `W 1%Z)%exp
  | <<%bin, e, (_ `W Z0)%exp
  | >>%bin, e, (_ `W Z0)%exp
  | `+%bin, (_ `S Z0)%exp, e
  | `+%bin, e, (_ `S Z0)%exp
  | `-%bin, e, (_ `S Z0)%exp
  | ×%bin, (_ `S 1%Z)%exp, e
  | ×%bin, e, (_ `S 1%Z)%exp
  | <<%bin, e, (_ `S Z0)%exp
  | >>%bin, e, (_ `S Z0)%exp
  | `&&%bin, Exp.Bool true, e
  | `&&%bin, e, Exp.Bool true
  | `||%bin, Exp.Bool false, e
  | `||%bin, e, Exp.Bool false
  | ×%bin, (_ `W Z0)%exp as e, _
  | ×%bin, _, (_ `W Z0)%exp as e
  | `&&%bin, Exp.Bool false as e, _
  | `&&%bin, _, Exp.Bool false as e
  | `||%bin, Exp.Bool true as e, _
  | `||%bin, _, Exp.Bool true as e => e
  | _, _, _ =>
      match eval_bin op e1 e2 with
      | Some e' => e'
      | None    => Exp.Bop t op e1 e2
      end
  end.

(** P4cub expression constant folding. *)
Fixpoint cf_e (e : Exp.t) : Exp.t :=
  match e with
  | Exp.Bool _
  | (_ `W _)%exp
  | (_ `S _)%exp
  | Exp.VarBit _ _ _
  | Exp.Error _
  | Exp.Var _ _ _ => e
  | Exp.Slice hi lo e =>
      let e' := cf_e e in
      match eval_slice hi lo e' with
      | Some e'' => e''
      | None     => Exp.Slice hi lo e'
      end
  | Exp.Cast t e =>
      let e' := cf_e e in
      match eval_cast t e' with
      | Some e'' => e''
      | None     => Exp.Cast t e'
      end
  | Exp.Uop t op e =>
      let e' := cf_e e in
      match eval_una op e with
      | Some e'' => e''
      | None     => Exp.Uop t op e'
      end
  | Exp.Bop t op e1 e2 =>
      optimize_bin t op (cf_e e1) (cf_e e2)
  | Exp.Lists ls es => Exp.Lists ls $ map cf_e es
  | Exp.Index t e1 e2 =>
      match cf_e e1, cf_e e2 with
      | Exp.Lists _ es as e1', (_ `W n)%exp as e2'
        => match nth_error es $ Z.to_nat n with
          | Some v => v
          | None => Exp.Index t e1' e2'
          end
      | e1', e2' => Exp.Index t e1' e2'
      end
  | Exp.Member t x e =>
      match cf_e e with
      | Exp.Lists _ es as e'
        =>  match nth_error es x with
           | Some v => v
           | None => Exp.Member t x e'
           end
      | e' => Exp.Member t x e'
      end
  end.
