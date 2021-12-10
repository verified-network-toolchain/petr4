Set Warnings "custom-entry-overridden,parsing".
Require Export Poulet4.P4cub.Syntax.AST.
Require Import Poulet4.P4cub.Syntax.IndPrincip
        Poulet4.P4cub.Syntax.CubNotations.
Import String AllCubNotations.

(** * Free Variables & Name Occurence *)

Definition
  list_of_option
  {U V : Type}
  (f : U -> list V)
  (o : option U) : list V :=
  match o with
  | Some u => f u
  | None   => []
  end.

Section FV.
  Context {tags_t : Type}.
  
  Fixpoint FVₑ (e : Expr.e tags_t) : list String.string :=
    match e with
    | <{ BOOL _ @ _ }>
    | <{ _ W _ @ _ }>
    | <{ _ S _ @ _ }>
    | <{ Error _ @ _ }>
    | <{ Matchkind _ @ _ }>             => []
    | <{ Var x:_ @ _ }>                 => [x]
    | <{ Slice e[_:_] @ _ }>
    | <{ Cast e:_ @ _ }>
    | <{ UOP _ e:_ @ _}>
    | <{ Mem e dot _ : _ @ _ }>
    | <{ Access e[_]: _ @ _ }>          => FVₑ e
    | <{ BOP e₁ _ e₂ : _ @ _ }>         => FVₑ e₁ ++ FVₑ e₂
    | <{ tup es @ _ }>
    | <{ Stack es:_ nextIndex:=_ @ _ }> => flat_map FVₑ es
    | <{ struct { es } @ _ }>           => flat_map (fun '(_,e) => FVₑ e) es
    | <{ hdr { es } valid := e @ _ }>
      => FVₑ e ++ flat_map (fun '(_,e) => FVₑ e) es
    end.

  Definition
    FV_paramarg
    '((PAIn e
      | PAOut e
      | PAInOut e
      | PADirLess e) : paramarg (Expr.e tags_t) (Expr.e tags_t))
    : list String.string := FVₑ e.
  
  Definition
    FV_arrowE
    '({| paramargs := es; rtrns := e |} : Expr.arrowE tags_t)
    : list String.string :=
    list_of_option FVₑ e ++ flat_map (FV_paramarg ∘ snd) es.
  
  Fixpoint FVₛ (s : Stmt.s tags_t) : list String.string :=
    match s with
    | -{ skip @ _ }-
    | -{ exit @ _ }-
    | -{ invoke _ @ _ }-             => []
    | -{ declare x : _ @ _ }-
    | Stmt.SHeaderStackOp x _ _ _    => [x]
    | -{ init x := e @ _ }-          => x :: FVₑ e
    | -{ asgn e₁ := e₂ @ _ }-        => FVₑ e₁ ++ FVₑ e₂
    | -{ if e then s₁ else s₂ @ _ }- => FVₑ e ++ FVₛ s₁ ++ FVₛ s₂
    | -{ s₁; s₂ @ _ }-               => FVₛ s₁ ++ FVₛ s₂
    | -{ b{ s }b }-                  => FVₛ s
    | Stmt.SExternMethodCall _ _ _ arr _
    | Stmt.SFunCall _ _ arr _        => FV_arrowE arr
    | -{ calling _ with es @ _ }-
    | -{ apply _ with _ & es @ _ }-  => flat_map (FV_paramarg ∘ snd) es
    | -{ return e @ _ }-             => list_of_option FVₑ e
    | Stmt.SSetValidity e _ _        => FVₑ e
    end.
End FV.

(* TODO: induction hypothesis. *)

Section Occurs.
  Context {tags_t : Type}.

  Variable x : string.

  (** A variable [x] Occurs in an expression. *)
  Inductive Occursₑ : Expr.e tags_t -> Prop :=
  | Occurs_var τ i :
      Occursₑ <{ Var x:τ @ i }>
  | Occurs_slice e hi lo i :
      Occursₑ e ->
      Occursₑ <{ Slice e [hi:lo] @ i }>
  | Occurs_cast τ e i :
      Occursₑ e ->
      Occursₑ <{ Cast e:τ @ i }>
  | Occurs_uop τ op e i :
      Occursₑ e ->
      Occursₑ <{ UOP op e:τ @ i }>
  | Occurs_bop τ op e₁ e₂ i :
      Occursₑ e₁ \/ Occursₑ e₂ ->
      Occursₑ <{ BOP e₁ op e₂ : τ @ i }>
  | Occurs_tuple es i :
      Exists Occursₑ es ->
      Occursₑ <{ tup es @ i }>
  | Occurs_struct es i :
      Exists (Occursₑ ∘ snd) es ->
      Occursₑ <{ struct { es } @ i }>
  | Occurs_header es e i :
      Exists (Occursₑ ∘ snd) es \/ Occursₑ e ->
      Occursₑ <{ hdr { es } valid:=e @ i }>
  | Occurs_member τ e y i :
      Occursₑ e ->
      Occursₑ <{ Mem e dot y : τ @ i }>
  | Occurs_stack τs es ni i :
      Exists Occursₑ es ->
      Occursₑ <{ Stack es:τs nextIndex:=ni @ i }>
  | Occurs_access τs e n i :
      Occursₑ e ->
      Occursₑ <{ Access e[n]:τs @ i }>.

  (** [x] occurs in call arguments. *)
  Definition
    Occurs_arrowE
    '({| paramargs := es; rtrns := e |} : Expr.arrowE tags_t) : Prop :=
    Exists (pred_paramarg_same Occursₑ ∘ snd) es \/
    match e with
    | Some e => Occursₑ e
    | None   => False
    end.
  
  (** A variable [x] Occurs in a statement. *)
  Inductive Occursₛ : Stmt.s tags_t -> Prop :=
  | Occurs_vardecl y et i :
      match et with
      | inl _ => x = y
      | inr e => x = y \/ Occursₑ e
      end ->
      Occursₛ -{ var x with et @ i }-
  | Occurs_assign e₁ e₂ i :
      Occursₑ e₁ \/ Occursₑ e₂ ->
      Occursₛ -{ asgn e₁ := e₂ @ i }-
  | Occurs_cond e s₁ s₂ i :
      Occursₑ e \/ Occursₛ s₁ \/ Occursₛ s₂ ->
      Occursₛ -{ if e then s₁ else s₂ @ i }-
  | Occursₛeq s₁ s₂ i :
      Occursₛ s₁ \/ Occursₛ s₂ ->
      Occursₛ -{ s₁; s₂ @ i }-
  | Occurs_block s :
      Occursₛ s ->
      Occursₛ -{ b{ s }b }-
  | Occurs_return e i :
      Occursₑ e ->
      Occursₛ (Stmt.SReturn (Some e) i)
  | Occursₛet_validity e b i :
    Occursₑ e ->
    Occursₛ (Stmt.SSetValidity e b i)
  | Occursₑxtern_method_call e m τs args i :
      Occurs_arrowE args ->
      Occursₛ (Stmt.SExternMethodCall e m τs args i)
  | Occurs_fun_call f τs args i :
      Occurs_arrowE args ->
      Occursₛ (Stmt.SFunCall f τs args i)
  | Occurs_act_call a es i :
      Exists (pred_paramarg_same Occursₑ ∘ snd) es ->
      Occursₛ (Stmt.SActCall a es i)
  | Occurs_apply y exts es i :
      Exists (pred_paramarg_same Occursₑ ∘ snd) es ->
      Occursₛ (Stmt.SApply y exts es i)
  | Occursₛtack_op o n i :
      Occursₛ (Stmt.SHeaderStackOp x o n i).

  Section FV_Occurs.
    Hint Rewrite in_app_iff : core.
    
    Lemma Occursₑ_FVₑ : forall e, Occursₑ e -> In x (FVₑ e).
    Proof.
      intros e Hoe;
        induction e as
          [ b i
          | w n i
          | w z i
          | t y i
          | e hi lo i IHe
          | t e i IHe
          | t o e IHe
          | t op e1 e2 i IHe1 IHe2
          | es i IHes
          | es i IHes
          | es e i IHe IHes
          | t y e i IHe
          | err i
          | mk i
          | ts es n i IHes
          | t e n i IHe
          ] using custom_e_ind
        ; inv Hoe; unravel in *;
          autorewrite with core; intuition.
      - rewrite Forall_forall in IHes.
        rewrite Exists_exists in H0.
        destruct H0 as (e & HInes & Hoe).
        rewrite in_flat_map; eauto.
    Admitted.
  End FV_Occurs.
End Occurs.
