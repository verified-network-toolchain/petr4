Set Warnings "custom-entry-overridden,parsing".
Require Import Poulet4.P4cub.Envn Poulet4.P4cub.Syntax.AST.

Module P := P4cub.
Module E := P.Expr.
Module F := P.F.

Import Env.EnvNotations P.P4cubNotations.

Section TypeSubstitution.
  Variable σ : Env.t string E.t. (* type environment. *)

  Fixpoint tsub_t (t : E.t) : E.t :=
    match t with
    | {{ Bool }}
    | {{ bit<_> }}
    | {{ int<_> }}
    | {{ error }}
    (*| {{ Str }}
    | {{ enum _ { _ } }}*)
    | {{ matchkind }}     => t
    | {{ tuple ts }}      => E.TTuple $ List.map tsub_t ts
    | {{ struct { ts } }} => E.TStruct $ F.map tsub_t ts
    | {{ hdr { ts } }}    => E.THeader $ F.map tsub_t ts
    | {{ stack ts[n] }}   => E.THeaderStack (F.map tsub_t ts) n
    | E.TVar X => match Env.find X σ with
                 | Some t => t
                 | None   => t
                 end
    end.
  (**[]*)

  Context {tags_t : Type}.
  
  Fixpoint tsub_e (e : E.e tags_t) : E.e tags_t :=
    match e with
    | <{ BOOL _ @ _ }>
    | <{ _ W _ @ _ }>
    | <{ _ S _ @ _ }>
    | <{ Var _ : _ @ _ }>
    | <{ Error _ @ _ }>
    (*| <{ Stri _ @ _ }>
    | <{ Enum _ dot _ @ _ }>*)
    | <{ Matchkind _ @ _ }> => e
    | <{ Slice e:t [hi:lo] @ i }> => E.ESlice (tsub_e e) (tsub_t t) hi lo i
    | <{ Cast e:t @ i }> => E.ECast (tsub_t t) (tsub_e e) i
    | <{ UOP op e:t @ i }> => E.EUop op (tsub_t t) (tsub_e e) i
    | <{ BOP e1:t1 op e2:t2 @ i }>
      => E.EBop op (tsub_t t1) (tsub_t t2) (tsub_e e1) (tsub_e e2) i
    | <{ tup es @ i }> => E.ETuple (List.map tsub_e es) i
    | <{ struct { es } @ i }>
      => E.EStruct (F.map (fun '(t,e) => (tsub_t t, tsub_e e)) es) i
    | <{ hdr { es } valid:=e @ i }>
      => E.EHeader
          (F.map (fun '(t,e) => (tsub_t t, tsub_e e)) es)
          (tsub_e e) i
    | <{ Mem e:t dot x @ i }>
      => E.EExprMember x (tsub_t t) (tsub_e e) i
    | <{ Stack hs:ts[n] nextIndex:=ni @ i }>
      => E.EHeaderStack (F.map tsub_t ts) (List.map tsub_e hs) n ni i
    | <{ Access e[n] @ i }> => E.EHeaderStackAccess (tsub_e e) n i
    end.
  (**[]*)
End TypeSubstitution.
