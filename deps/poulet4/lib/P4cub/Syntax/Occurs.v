Set Warnings "custom-entry-overridden,parsing".
Require Import Poulet4.P4cub.Syntax.AST
        Poulet4.P4cub.Syntax.CubNotations.
Import AllCubNotations.

(* TODO: induction hypothesis. *)

Section Occurs.
  Context {tags_t : Type}.

  Variable x : string.

  (** A variable [x] Occurs in an expression. *)
  Inductive Occurs_e : Expr.e tags_t -> Prop :=
  | Occurs_var τ i :
      Occurs_e <{ Var x:τ @ i }>
  | Occurs_slice e hi lo i :
      Occurs_e e ->
      Occurs_e <{ Slice e [hi:lo] @ i }>
  | Occurs_cast τ e i :
      Occurs_e e ->
      Occurs_e <{ Cast e:τ @ i }>
  | Occurs_uop τ op e i :
      Occurs_e e ->
      Occurs_e <{ UOP op e:τ @ i }>
  | Occurs_bop τ op e₁ e₂ i :
      Occurs_e e₁ \/ Occurs_e e₂ ->
      Occurs_e <{ BOP e₁ op e₂ : τ @ i }>
  | Occurs_tuple es i :
      Exists Occurs_e es ->
      Occurs_e <{ tup es @ i }>
  | Occurs_struct es i :
      Exists (Occurs_e ∘ snd) es ->
      Occurs_e <{ struct { es } @ i }>
  | Occurs_header es e i :
      Exists (Occurs_e ∘ snd) es \/ Occurs_e e ->
      Occurs_e <{ hdr { es } valid:=e @ i }>
  | Occurs_member τ e x i :
      Occurs_e e ->
      Occurs_e <{ Mem e dot x : τ @ i }>
  | Occurs_stack τs es ni i :
      Exists Occurs_e es ->
      Occurs_e <{ Stack es:τs nextIndex:=ni @ i }>
  | Occurs_access τs e n i :
      Occurs_e e ->
      Occurs_e <{ Access e[n]:τs @ i }>.

  (* TODO: arguments and constructor arguments
     occurence check. *)
  
  (** A variable [x] Occurs in a statement. *)
  (* TODO: cases with [arrow]:
     function, action calls,
     control, parser apply, etc. *)
  Inductive Occurs_s : Stmt.s tags_t -> Prop :=
  | Occurs_vardecl y et i :
      match et with
      | inl _ => x = y
      | inr e => x = y \/ Occurs_e e
      end ->
      Occurs_s -{ var x with et @ i }-
  | Occurs_assign e₁ e₂ i :
      Occurs_e e₁ \/ Occurs_e e₂ ->
      Occurs_s -{ asgn e₁ := e₂ @ i }-
  | Occurs_cond e s₁ s₂ i :
      Occurs_e e \/ Occurs_s s₁ \/ Occurs_s s₂ ->
      Occurs_s -{ if e then s₁ else s₂ @ i }-
  | Occurs_seq s₁ s₂ i :
      Occurs_s s₁ \/ Occurs_s s₂ ->
      Occurs_s -{ s₁; s₂ @ i }-
  | Occurs_block s :
      Occurs_s s ->
      Occurs_s -{ b{ s }b }-
  | Occurs_return e i :
      Occurs_e e ->
      Occurs_s (Stmt.SReturn (Some e) i)
  | Occurs_set_validity e b i :
    Occurs_e e ->
    Occurs_s (Stmt.SSetValidity e b i).
End Occurs.
