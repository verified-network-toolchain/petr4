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

Fixpoint FVₑ (e : Expr.e) : list nat :=
  match e with
  | Expr.Bool _
  | (_ `W _)%expr
  | (_ `S _)%expr
  | Expr.Error _ => []
  | Expr.Var _ x => [x]
  | Expr.Slice e _ _
  | Expr.Cast _ e
  | Expr.Uop _ _ e
  | Expr.Member _ _ e  => FVₑ e
  | Expr.Bop _ _ e₁ e₂ => FVₑ e₁ ++ FVₑ e₂
  | Expr.Struct es e
    => list_of_option FVₑ e ++ flat_map FVₑ es
  end.

Definition
  FV_paramarg
  '((PAIn e
    | PAOut e
    | PAInOut e) : paramarg Expr.e Expr.e)
  : list nat := FVₑ e.

Definition
  FV_arrowE
  '({| paramargs := es; rtrns := e |} : Expr.arrowE)
  : list nat :=
  list_of_option FVₑ e ++ flat_map FV_paramarg es.

Fixpoint FVₛ (s : Stmt.s) : list nat :=
  match s with
  | Stmt.Skip
  | Stmt.Exit
  | Stmt.Invoke _
  | Stmt.Return None
  | Stmt.Var (inl _)            => []
  | Stmt.Return (Some e)
  | Stmt.Var (inr e)            => FVₑ e
  | (e₁ `:= e₂)%stmt            => FVₑ e₁ ++ FVₑ e₂
  | (If e Then s₁ Else s₂)%stmt => FVₑ e ++ FVₛ s₁ ++ FVₛ s₂
  | (s₁ `; s₂)%stmt             => FVₛ s₁ ++ FVₛ s₂
  | Stmt.Block s                => FVₛ s
  | Stmt.ExternMethodCall _ _ _ arr
  | Stmt.FunCall _ _ arr        => FV_arrowE arr
  | Stmt.Apply _ _ es           => flat_map FV_paramarg es
  | Stmt.ActCall _ cs ds        => flat_map FVₑ cs ++ flat_map FV_paramarg ds
  end.

(* TODO: induction hypothesis. *)
Section Occurs.
  Variable x : nat.

  (** A variable [x] Occurs in an expression. *)
  Inductive Occursₑ : Expr.e -> Prop :=
  | Occurs_var τ :
    Occursₑ (Expr.Var τ x)
  | Occurs_slice e hi lo :
    Occursₑ e ->
    Occursₑ (Expr.Slice e hi lo)
  | Occurs_cast τ e :
    Occursₑ e ->
    Occursₑ (Expr.Cast τ e)
  | Occurs_uop τ op e :
    Occursₑ e ->
    Occursₑ (Expr.Uop τ op e)
  | Occurs_bop τ op e₁ e₂ :
    Occursₑ e₁ \/ Occursₑ e₂ ->
    Occursₑ (Expr.Bop τ op e₁ e₂)
  | Occurs_struct es e :
    Exists Occursₑ es \/ OExists Occursₑ e ->
    Occursₑ (Expr.Struct es e)
  | Occurs_member τ e y :
    Occursₑ e ->
    Occursₑ (Expr.Member τ y e).

  (** [x] occursn call arguments. *)
  Definition
    Occurs_arrowE
    '({| paramargs := es; rtrns := e |} : Expr.arrowE) : Prop :=
    Exists (pred_paramarg_same Occursₑ) es \/
    match e with
    | Some e => Occursₑ e
    | None   => False
    end.
  
  (** A variable [x] Occursn a statement. *)
  Inductive Occursₛ : Stmt.s -> Prop :=
  | Occurs_vardecl e :
    Occursₑ e ->
    Occursₛ (Stmt.Var (inr e))
  | Occurs_assign e₁ e₂ :
    Occursₑ e₁ \/ Occursₑ e₂ ->
    Occursₛ (e₁ `:= e₂)%stmt
  | Occurs_cond e s₁ s₂ :
    Occursₑ e \/ Occursₛ s₁ \/ Occursₛ s₂ ->
    Occursₛ (If e Then s₁ Else s₂)%stmt
  | Occursₛ_seq s₁ s₂ :
    Occursₛ s₁ \/ Occursₛ s₂ ->
    Occursₛ (s₁ `; s₂ )%stmt
  | Occurs_block s :
    Occursₛ s ->
    Occursₛ (Stmt.Block s)
  | Occurs_return e :
    Occursₑ e ->
    Occursₛ(Stmt.Return (Some e))
  | Occursₑ_extern_method_call e m τs args :
    Occurs_arrowE args ->
    Occursₛ (Stmt.ExternMethodCall e m τs args)
  | Occurs_fun_call f τs args :
    Occurs_arrowE args ->
    Occursₛ (Stmt.FunCall f τs args)
  | Occurs_act_call a cs ds :
    Exists Occursₑ cs \/ Exists (pred_paramarg_same Occursₑ) ds ->
    Occursₛ (Stmt.ActCall a cs ds)
  | Occurs_apply y exts es :
    Exists (pred_paramarg_same Occursₑ) es ->
    Occursₛ (Stmt.Apply y exts es).

  Section FV_Occurs.
    Hint Rewrite in_app_iff : core.
    
    Lemma Occursₑ_FVₑ : forall e, Occursₑ e -> In x (FVₑ e).
    Proof.
      intros e Hoe;
        induction e as
        [ b
        | w n
        | w z
        | t y
        | e hi lo He
        | t e He
        | t o e He
        | t op e1 e2 He1 He2
        | es e Hes He
        | t y e He
        | err] using custom_e_ind; inv Hoe; unravel in *;
        autorewrite with core; intuition.
      - rewrite Forall_forall in Hes.
        rewrite Exists_exists in H.
        destruct H as (e' & HInes & Hoe).
        rewrite in_flat_map; eauto.
      - destruct e as [e |]; inv He; inv H; cbn; auto.
    Qed.

    Local Hint Constructors Occursₑ : core.
    Local Hint Constructors OExists : core.
    
    Lemma FVₑ_Occursₑ : forall e, In x (FVₑ e) -> Occursₑ e.
    Proof.
      intros e Hoe;
        induction e as
        [ b
        | w n
        | w z
        | t y
        | e hi lo He
        | t e He
        | t o e He
        | t op e1 e2 He1 He2
        | es e Hes He
        | t y e He
        | err] using custom_e_ind;
        unravel in *; autorewrite with core in *;
        try contradiction; eauto;
        intuition; subst; auto.
      - constructor.
        destruct e as [e |]; inv He; cbn in *; auto || contradiction.
      - constructor; left; clear dependent e.
        rewrite Forall_forall in Hes.
        rewrite Exists_exists.
        rewrite in_flat_map in H.
        destruct H as (e & ein & fvin); eauto.
    Qed.

    Local Hint Resolve Occursₑ_FVₑ : core.
    Local Hint Resolve FVₑ_Occursₑ : core.
    
    Lemma Occursₑ_FVₑ_iff : forall e,
        Occursₑ e <-> In x (FVₑ e).
    Proof.
      intuition.
    Qed.

    Lemma Occurs_FV_arrowE : forall arr,
        Occurs_arrowE arr -> In x (FV_arrowE arr).
    Proof.
      intros [es e] H;
        unfold Occurs_arrowE, FV_arrowE in *;
        unravel in *; autorewrite with core.
      destruct H as [H | H].
      - right. rewrite in_flat_map_Exists.
        rewrite Exists_exists in *.
        destruct H as (pae & Hines & Hopae).
        exists pae; simpl in *.
        destruct pae;
          unfold pred_paramarg_same,
          pred_paramarg, FV_paramarg in *; auto.
      - destruct e as [e |]; unravel in *; auto.
    Qed.

    Lemma FV_Occurs_arrowE : forall arr,
        In x (FV_arrowE arr) -> Occurs_arrowE arr.
    Proof.
      intros [es e] H;
        unfold Occurs_arrowE, FV_arrowE in *;
        unravel in *; autorewrite with core in *.
      destruct H as [H | H].
      - destruct e as [e |]; unravel in *; auto.
      - left. rewrite in_flat_map_Exists in H.
        rewrite Exists_exists in *.
        destruct H as (pae & Hines & Hopae).
        exists pae; simpl in *.
        destruct pae;
          unfold pred_paramarg_same,
          pred_paramarg, FV_paramarg in *; auto.
    Qed.

    Local Hint Resolve Occurs_FV_arrowE : core.
    Local Hint Resolve FV_Occurs_arrowE : core.
    
    Lemma Occurs_FV_arrowE_iff : forall arr,
        Occurs_arrowE arr <-> In x (FV_arrowE arr).
    Proof.
      intuition.
    Qed.

    Lemma Occursₛ_FVₛ : forall s, Occursₛ s -> In x (FVₛ s).
    Proof.
      intros s Hos;
        induction s
        as [ | [t | e]
           | e1 e2
           | e s1 Hs1 s2 Hs2
           | s1 Hs1 s2 Hs2
           | s Hs
           | ext f ts arr
           | f ts arr
           | a cs ds
           | [e |] |
           | t
           | z exts es]; unravel in *; inv Hos;
        auto; autorewrite with core; intuition.
      - left; rewrite in_flat_map_Exists.
        rewrite Exists_exists in *.
        destruct H as (e & Hincs & Hoe).
        exists e; simpl in *; auto.
      - right; rewrite in_flat_map_Exists.
        rewrite Exists_exists in *.
        destruct H as (pae & Hines & Hopae).
        exists pae; simpl in *.
        destruct pae;
          unfold pred_paramarg_same,
          pred_paramarg, FV_paramarg in *; auto.
      - rewrite in_flat_map_Exists.
        rewrite Exists_exists in *.
        destruct H0 as (pae & Hines & Hopae).
        exists pae; simpl in *.
        destruct pae;
          unfold pred_paramarg_same,
          pred_paramarg, FV_paramarg in *; auto.
    Qed.

    Local Hint Constructors Occursₛ : core.
    
    Lemma FVₛ_Occursₛ : forall s, In x (FVₛ s) -> Occursₛ s.
    Proof.
      intros s Hin;
        induction s
        as [ | [t | e]
           | e1 e2
           | e s1 Hs1 s2 Hs2
           | s1 Hs1 s2 Hs2
           | s Hs
           | ext f ts arr
           | f ts arr
           | a cs ds
           | [e |] |
           | t
           | z exts es]; unravel in *;
        autorewrite with core in *;
        try contradiction;
        intuition; subst; eauto.
      - constructor; left.
        rewrite in_flat_map_Exists in H.
        rewrite Exists_exists in *.
        destruct H as (e & Hincs & Hoe); eauto.
      - constructor; right.
        rewrite in_flat_map_Exists in H.
        rewrite Exists_exists in *.
        destruct H as (pae & Hines & Hopae).
        exists pae; unravel in *.
        destruct pae;
          unfold pred_paramarg_same,
          pred_paramarg, FV_paramarg in *; auto.
      - constructor.
        rewrite in_flat_map_Exists in Hin.
        rewrite Exists_exists in *.
        destruct Hin as (pae & Hines & Hopae).
        exists pae; unravel in *.
        destruct pae;
          unfold pred_paramarg_same,
          pred_paramarg, FV_paramarg in *; auto.
    Qed.

    Local Hint Resolve Occursₛ_FVₛ : core.
    Local Hint Resolve FVₛ_Occursₛ : core.

    Lemma Occursₛ_FVₛ_iff : forall s,
        Occursₛ s <-> In x (FVₛ s).
    Proof.
     intuition.
    Qed.
  End FV_Occurs.
End Occurs.
