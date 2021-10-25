Require Import Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.SmallStep.Util
        Coq.ZArith.BinInt.
Module E := P4cub.Expr.
Import P4cub.P4cubNotations.

Section ConstFold.
  Context {tags_t : Type}.

  (** Binary operation optimizations. *)
  Definition optimize_bop
             (op : E.bop) (t1 t2 : E.t)
             (e1 e2 : E.e tags_t) (i : tags_t)
    : E.e tags_t :=
    match op, e1, e2 with
    | +{ + }+, <{ _ W Z0 @ _ }>, e
    | +{ + }+, e, <{ _ W Z0 @ _ }>
    | +{ - }+, e, <{ _ W Z0 @ _ }>
    | +{ × }+, E.EBit _ 1%Z _, e
    | +{ × }+, e, E.EBit _ 1%Z _
    | +{ << }+, e, <{ _ W Z0 @ _ }>
    | +{ >> }+, e, <{ _ W Z0 @ _ }>
    | +{ + }+, <{ _ S Z0 @ _ }>, e
    | +{ + }+, e, <{ _ S Z0 @ _ }>
    | +{ - }+, e, <{ _ S Z0 @ _ }>
    | +{ × }+, E.EInt _ 1%Z _, e
    | +{ × }+, e, E.EInt _ 1%Z _
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
      | None     => <{ BOP e1:t1 op e2:t2 @ i }>
      end
    end.
  
  (** P4cub expression constant folding. *)
  Fixpoint cf_e (e : E.e tags_t) : E.e tags_t :=
    match e with
    | <{ BOOL _ @ _ }>
    | <{ _ W _ @ _ }>
    | <{ _ S _ @ _ }>
    | <{ Error _ @ _ }>
    | <{ Matchkind _ @ _ }>
    | <{ Var _ : _ @ _ }> => e
    | <{ Slice e:t [hi:lo] @ i }> =>
      let e' := cf_e e in
      match eval_slice hi lo e' with
      | Some e'' => e''
      | None     => <{ Slice e':t [hi:lo] @ i }>
      end
    | <{ Cast e:t @ i }> =>
      let e' := cf_e e in
      match eval_cast t e' with
      | Some e'' => e''
      | None     => <{ Cast e':t @ i }>
      end
    | <{ UOP op e:t @ i }> =>
      let e' := cf_e e in
      match eval_uop op e with
      | Some e'' => e''
      | None     => <{ UOP op e':t @ i }>
      end
    | <{ BOP e1:t1 op e2:t2 @ i }> =>
      optimize_bop op t1 t2 (cf_e e1) (cf_e e2) i
    | <{ tup es @ i }> => E.ETuple (map cf_e es) i
    | <{ struct { es } @ i }> =>
      E.EStruct (F.map (fun '(t,e) => (t,cf_e e)) es) i
    | <{ hdr { es } valid:=e @ i }> =>
      E.EHeader (F.map (fun '(t,e) => (t,cf_e e)) es) (cf_e e) i
    | <{ Mem e:t dot x @ i }> =>
      let e' := cf_e e in
      match eval_member x e' with
      | Some e'' => e''
      | None     => <{ Mem e':t dot x @ i }>
      end
    | <{ Stack hs:ts [n] nextIndex:=ni @ i }> =>
      E.EHeaderStack ts (map cf_e hs) n ni i
    | <{ Access e[n] @ i }> =>
      let e' := cf_e e in
      match eval_access e' n with
      | Some e'' => e''
      | None     => <{ Access e'[n] @ i }>
      end
    end.
End ConstFold.
