Require Import Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Semantics.Dynamic.SmallStep.Util
        Coq.ZArith.BinInt.
Import AllCubNotations.

Section ConstFold.
  Context {tags_t : Type}.

  (** Binary operation optimizations. *)
  Definition optimize_bop
             (t : Expr.t) (op : Expr.bop)
             (e1 e2 : Expr.e tags_t) (i : tags_t)
    : Expr.e tags_t :=
    match op, e1, e2 with
    | +{ + }+, <{ _ W Z0 @ _ }>, e
    | +{ + }+, e, <{ _ W Z0 @ _ }>
    | +{ - }+, e, <{ _ W Z0 @ _ }>
    | +{ × }+, Expr.EBit _ 1%Z _, e
    | +{ × }+, e, Expr.EBit _ 1%Z _
    | +{ << }+, e, <{ _ W Z0 @ _ }>
    | +{ >> }+, e, <{ _ W Z0 @ _ }>
    | +{ + }+, <{ _ S Z0 @ _ }>, e
    | +{ + }+, e, <{ _ S Z0 @ _ }>
    | +{ - }+, e, <{ _ S Z0 @ _ }>
    | +{ × }+, Expr.EInt _ 1%Z _, e
    | +{ × }+, e, Expr.EInt _ 1%Z _
    | +{ << }+, e, <{ _ S Z0 @ _ }>
    | +{ >> }+, e, <{ _ S Z0 @ _ }>
    | +{ && }+, <{ BOOL true @ _ }>, e
    | +{ && }+, e, <{ BOOL true @ _ }>
    | +{ || }+, <{ BOOL false @ _ }>, e
    | +{ || }+, e, <{ BOOL false @ _ }>
    | +{ × }+, <{ _ W Z0 @ _ }> as e, _
    | +{ × }+, _, <{ _ W Z0 @ _ }> as e
    | +{ && }+, <{ BOOL false @ _ }> as e, _
    | +{ && }+, _, <{ BOOL false @ _ }> as e
    | +{ || }+, <{ BOOL true @ _ }> as e, _
    | +{ || }+, _, <{ BOOL true @ _ }> as e => e
    | _, _, _ =>
      match eval_bop op e1 e2 i with
      | Some e' => e'
      | None     => <{ BOP e1 op e2 : t @ i }>
      end
    end.
  
  (** P4cub expression constant folding. *)
  Fixpoint cf_e (e : Expr.e tags_t) : Expr.e tags_t :=
    match e with
    | <{ BOOL _ @ _ }>
    | <{ _ W _ @ _ }>
    | <{ _ S _ @ _ }>
    | <{ Error _ @ _ }>
    | <{ Var _ : _ @ _ }> => e
    | <{ Slice e [hi:lo] @ i }> =>
      let e' := cf_e e in
      match eval_slice hi lo e' with
      | Some e'' => e''
      | None     => <{ Slice e' [hi:lo] @ i }>
      end
    | <{ Cast e:t @ i }> =>
      let e' := cf_e e in
      match eval_cast t e' with
      | Some e'' => e''
      | None     => <{ Cast e':t @ i }>
      end
    | <{ UOP op e : t @ i }> =>
      let e' := cf_e e in
      match eval_uop op e with
      | Some e'' => e''
      | None     => <{ UOP op e' : t @ i }>
      end
    | <{ BOP e1 op e2 : t @ i }> =>
      optimize_bop t op (cf_e e1) (cf_e e2) i
    | <{ tup es @ i }> => Expr.ETuple (map cf_e es) i
    | <{ struct { es } @ i }> => Expr.EStruct (F.map cf_e es) i
    | <{ hdr { es } valid:=e @ i }> =>
      Expr.EHeader (F.map cf_e es) (cf_e e) i
    | <{ Mem e dot x : t @ i }> =>
      let e' := cf_e e in
      match eval_member x e' with
      | Some e'' => e''
      | None     => <{ Mem e' dot x : t @ i }>
      end
    | <{ Stack hs:ts nextIndex:=ni @ i }> =>
      Expr.EHeaderStack ts (map cf_e hs) ni i
    | <{ Access e[n] : ts @ i }> =>
      let e' := cf_e e in
      match eval_access e' n with
      | Some e'' => e''
      | None     => <{ Access e'[n] : ts @ i }>
      end
    end.
End ConstFold.
