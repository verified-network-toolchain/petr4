Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.Syntax.Syntax Poulet4.P4cub.Envn
        Poulet4.P4cub.BigStep.Value.Syntax
        Poulet4.P4cub.BigStep.Semantics
        Poulet4.P4cub.BigStep.IndPrincip.
Import AllCubNotations Val.ValueNotations
       Val.LValueNotations F.FieldTactics Step.

Section Properties.
  Lemma lv_update_sub_env : forall lv v ϵ,
    ϵ ⊆ lv_update lv v ϵ.
  Proof.
    intro lv;
      induction lv; intros v eps; simpl.
    - (* not generally true. *) admit.
  Abort.
  
  Context {tags_t : Type}.
  Local Hint Resolve Env.scope_shadow_sub_env : core.
  Local Hint Resolve Utils.Forall2_dumb : core.
  Local Hint Constructors expr_big_step : core.
  
  Lemma expr_big_step_sub_env : forall ϵ ϵ' (e : Expr.e tags_t) v,
      ϵ ⊆ ϵ' -> ⟨ ϵ, e ⟩ ⇓ v -> ⟨ ϵ', e ⟩ ⇓ v.
  Proof.
    intros eps eps' e v Heps Hev.
    induction Hev
      as [ eps b i 
         | eps w n i
         | eps w z i
         | eps x t i v Hxv
         | eps e hi lo i v v' Hslice Hev IHev
         | eps t e i v v' Hcast Hev IHev
         | eps err i
         | eps mk i
         | eps t op e i v v' Huop Hev IHev
         | eps t op e1 e2 i v v1 v2 Hbop Hev1 IHev1 Hev2 IHev2
         | eps t e x i v v' Hmem Hev IHev
         | eps es i vs Hevs IHevs
         | eps es i vs Hevs IHevs
         | eps es e i b vs Hevs IHevs Hev IHev
         | eps ts es ni i vss Hevsss IHevsss
         | eps e i n ni ts vss b vs Haccess Hevss IHevss
         ] using custom_expr_big_step_ind; eauto.
    - constructor; unfold F.relfs, F.relf in *; unravel in *.
      rewrite Utils.Forall2_conj in *.
      firstorder eauto.
    - constructor; auto; unfold F.relfs, F.relf in *; unravel in *.
      rewrite Utils.Forall2_conj in *.
      firstorder eauto.
  Qed.

  Local Hint Resolve expr_big_step_sub_env : core.
  Local Hint Constructors stmt_big_step : core.
  
  Lemma stmt_big_step_sub_env :
    forall ϵ₁ ϵ₁' ϵ₂ ϵ₂' (s : Stmt.s tags_t) pkt pkt' fs cx sig,
      ϵ₁ ⊆ ϵ₂ -> ϵ₁' ⊆ ϵ₂' ->
      ⟪ pkt , fs , ϵ₁ , cx , s ⟫ ⤋ ⟪ ϵ₁' , sig , pkt' ⟫ ->
      ⟪ pkt , fs , ϵ₂ , cx , s ⟫ ⤋ ⟪ ϵ₂' , sig , pkt' ⟫.
  Proof.
    intros eps1 eps1' eps2 eps2' s pkt pkt' fs cx sig Heps Heps' Hsbs.
    induction Hsbs; eauto 4.
    (* TODO: need a notion of [env₁ ⊆ env₂]
       that keeps track of exactly which bindings
       [env₂] has that [env₁] does not. *)
  Abort.
End Properties.
