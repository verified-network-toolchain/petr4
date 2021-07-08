Set Warnings "-custom-entry-overridden".
Require Import
        Poulet4.P4cub.Envn
        Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Static.Util
        Poulet4.P4cub.Static.Typing
        Poulet4.P4cub.Static.IndPrincip.
Import P.P4cubNotations.

(** TODO *)
Section TypeOf.
  Context {tags_t : Type}.
  
  Fail Fixpoint type_of_expr (Γ : gamma) (e : E.e tags_t) : option E.t :=
    match e with
    | <{ BOOL _ @ _ }> => Some {{ Bool }}
    | <{ w W n @ _ }> => None
    end.
End TypeOf.
