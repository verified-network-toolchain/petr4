Set Warnings "custom-entry-overridden,parsing".
Require Import Poulet4.P4cub.Envn Poulet4.P4cub.Syntax.AST
        Poulet4.P4cub.Syntax.CubNotations.
Import AllCubNotations Env.EnvNotations.

Section TypeSubstitution.
  Variable σ : Env.t string Expr.t. (* type environment. *)

  Fixpoint tsub_t (t : Expr.t) : Expr.t :=
    match t with
    | {{ Bool }}
    | {{ bit<_> }}
    | {{ int<_> }}
    | {{ error }}
    (*| {{ Str }}
    | {{ enum _ { _ } }}*)
    | {{ matchkind }}     => t
    | {{ tuple ts }}      => Expr.TTuple $ List.map tsub_t ts
    | {{ struct { ts } }} => Expr.TStruct $ F.map tsub_t ts
    | {{ hdr { ts } }}    => Expr.THeader $ F.map tsub_t ts
    | {{ stack ts[n] }}   => Expr.THeaderStack (F.map tsub_t ts) n
    | Expr.TVar X => match Env.find X σ with
                 | Some t => t
                 | None   => t
                 end
    end.
  (**[]*)

  Context {tags_t : Type}.
  
  Fixpoint tsub_e (e : Expr.e tags_t) : Expr.e tags_t :=
    match e with
    | <{ BOOL _ @ _ }>
    | <{ _ W _ @ _ }>
    | <{ _ S _ @ _ }>
    | <{ Var _ : _ @ _ }>
    | <{ Error _ @ _ }>
    (*| <{ Stri _ @ _ }>
    | <{ Enum _ dot _ @ _ }>*)
    | <{ Matchkind _ @ _ }> => e
    | <{ Slice e:t [hi:lo] @ i }> => Expr.ESlice (tsub_e e) (tsub_t t) hi lo i
    | <{ Cast e:t @ i }> => Expr.ECast (tsub_t t) (tsub_e e) i
    | <{ UOP op e:t @ i }> => Expr.EUop op (tsub_t t) (tsub_e e) i
    | <{ BOP e1:t1 op e2:t2 @ i }>
      => Expr.EBop op (tsub_t t1) (tsub_t t2) (tsub_e e1) (tsub_e e2) i
    | <{ tup es @ i }> => Expr.ETuple (List.map tsub_e es) i
    | <{ struct { es } @ i }>
      => Expr.EStruct (F.map (fun '(t,e) => (tsub_t t, tsub_e e)) es) i
    | <{ hdr { es } valid:=e @ i }>
      => Expr.EHeader
          (F.map (fun '(t,e) => (tsub_t t, tsub_e e)) es)
          (tsub_e e) i
    | <{ Mem e:t dot x @ i }>
      => Expr.EExprMember x (tsub_t t) (tsub_e e) i
    | <{ Stack hs:ts[n] nextIndex:=ni @ i }>
      => Expr.EHeaderStack (F.map tsub_t ts) (List.map tsub_e hs) n ni i
    | <{ Access e[n] @ i }> => Expr.EHeaderStackAccess (tsub_e e) n i
    end.
  (**[]*)
End TypeSubstitution.
