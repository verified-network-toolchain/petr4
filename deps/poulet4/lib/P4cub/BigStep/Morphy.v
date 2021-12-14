Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.Syntax.Syntax Poulet4.P4cub.Envn
        Poulet4.P4cub.BigStep.Value.Syntax
        Poulet4.P4cub.BigStep.Semantics
        Poulet4.P4cub.BigStep.IndPrincip
        Coq.Classes.Morphisms.
Import AllCubNotations Val.ValueNotations
       Val.LValueNotations F.FieldTactics Step.

Section EnvEq.
  Lemma eq_env_lv_lookup : forall lv ϵ ϵ',
      ϵ ≝ ϵ' -> lv_lookup ϵ lv = lv_lookup ϵ' lv.
  Proof.
    intros lv g g' Hg;
      rewrite Env.find_eq_env in Hg;
      induction lv
        as [x | lv IHlv hi lo
            | lv IHlv x | lv IHlv n]; unravel;
        try rewrite IHlv; auto.
  Qed.

  Local Hint Resolve eq_env_lv_lookup : core.
  Local Hint Resolve Env.bind_eq_env : core.
  
  Lemma eq_env_lv_update : forall lv v ϵ ϵ',
      ϵ ≝ ϵ' -> lv_update lv v ϵ ≝ lv_update lv v ϵ'.
  Proof.
    intro lv;
      induction lv
      as [x | lv IHlv hi lo
          | lv IHlv x | lv IHlv n];
      intros v g g' Hg; unravel; auto;
        try (destruct v; erewrite eq_env_lv_lookup by eauto;
             destruct (lv_lookup g' lv) as [[] |] eqn:Heqv'; auto).
  Qed.

  Local Hint Resolve eq_env_lv_update : core.

  Lemma eq_env_copy_in : forall argsv ϵ ϵ' closure,
      ϵ ≝ ϵ' -> copy_in argsv ϵ closure = copy_in argsv ϵ' closure.
  Proof.
    intros argsv g g' closure Hg;
      unfold copy_in, F.fold;
      induction argsv
        as [| [x [v | lv | lv | v]] vs IHvs];
      unravel; try erewrite eq_env_lv_lookup by eauto;
        try rewrite IHvs; eauto.
  Qed.

  Lemma eq_env_copy_out_l : forall argsv ϵ₁ ϵ₁' ϵ₂,
      ϵ₁ ≝ ϵ₁' -> copy_out argsv ϵ₁ ϵ₂ = copy_out argsv ϵ₁' ϵ₂.
  Proof.
    intros argsv e1 e1' e2 He1; pose proof He1 as He1';
      rewrite Env.find_eq_env in He1';
      unfold copy_out, Field.fold;
      induction argsv
        as [| [x [v | lv | lv | v]] vs IHvs];
      unravel; auto; try rewrite He1';
        try destruct (Env.find x e1') as [v1 |] eqn:Heqv1;
        try rewrite IHvs; auto.
  Qed.

  Lemma eq_env_copy_out_r : forall argsv ϵ₁ ϵ₂ ϵ₂',
      ϵ₂ ≝ ϵ₂' -> copy_out argsv ϵ₁ ϵ₂ ≝ copy_out argsv ϵ₁ ϵ₂'.
  Proof.
    intros argsv e1 e2 e2' He2; pose proof He2 as He2';
      rewrite Env.find_eq_env in He2';
      unfold copy_out, Field.fold;
      induction argsv
        as [| [x [v | lv | lv | v]] vs IHvs];
      unravel; auto;
        try destruct (Env.find x e1) as [v1 |] eqn:Heqv1; auto.
  Qed.
  
  Context {tags_t : Type}.

  Local Hint Resolve Utils.Forall2_dumb : core.
  Local Hint Constructors expr_big_step : core.
  Hint Rewrite Utils.Forall2_conj : core.
  Local Hint Unfold Field.relfs : core.
  Local Hint Unfold Field.relf : core.

  Ltac destr_conj :=
    match goal with
    | H: ?P /\ ?Q |- _ => destruct H as [? ?]
    end.
  
  Lemma eq_env_expr_big_step : forall ϵ₁ ϵ₂ (e : Expr.e tags_t) v,
      ϵ₁ ≝ ϵ₂ -> ⟨ ϵ₁, e ⟩ ⇓ v -> ⟨ ϵ₂, e ⟩ ⇓ v.
  Proof.
    intros g1 g2 e v Hg Hev;
      induction Hev using custom_expr_big_step_ind;
      autounfold with * in *; unravel in *;
        autorewrite with core in *;
        repeat destr_conj; eauto.
    - unfold Env.eq_env, Env.sub_env in *.
      intuition.
    - constructor; unfold F.relfs, F.relf in *;
        unravel in *; autorewrite with core; eauto.
    - constructor; unfold F.relfs, F.relf in *;
        unravel in *; autorewrite with core; eauto.
  Qed.

  Local Hint Resolve eq_env_expr_big_step : core.
  Local Hint Constructors parser_expr_big_step : core.

  Lemma eq_env_parser_expr_big_step :
    forall ϵ₁ ϵ₂ (e : AST.Parser.e tags_t) st,
      ϵ₁ ≝ ϵ₂ -> ⦑ ϵ₁ , e ⦒ ⇓ st -> ⦑ ϵ₂ , e ⦒ ⇓ st.
  Proof.
    intros g1 g2 e v Hg Hev;
      induction Hev using custom_parser_expr_big_step_ind;
      cbn in *; autorewrite with core in *;
        repeat destr_conj; eauto.
    constructor; eauto 2; cbn.
    autorewrite with core in *.
    split; eauto 2.
  Qed.
    
  Local Hint Constructors stmt_big_step : core.
  Local Hint Resolve Env.shadow_eq_env_l : core.
  Local Hint Resolve Env.shadow_eq_env_r : core.
  
  Lemma eq_env_stmt_big_step :
    forall (s : Stmt.s tags_t) ϵ₁ ϵ₁' ϵ₂ fs cx pkt pkt' sig,
      ϵ₁ ≝ ϵ₂ ->
      ⟪ pkt , fs , ϵ₁ , cx , s ⟫ ⤋ ⟪ ϵ₁' , sig , pkt' ⟫ ->
      exists ϵ₂', ⟪ pkt , fs , ϵ₂ , cx , s ⟫ ⤋ ⟪ ϵ₂' , sig , pkt' ⟫ /\ ϵ₁' ≝ ϵ₂'.
  Proof.
    intros s g1 g1' g2 fs cx pkt pkt' sig Hg Hsbs;
      generalize dependent g2;
      induction Hsbs; intros g2 Hg; eauto 3.
    - pose proof IHHsbs1 _ Hg as IH1; clear IHHsbs1.
      destruct IH1 as (g' & Hs1g' & Hg').
      pose proof IHHsbs2 _ Hg' as IH2; clear IHHsbs2.
      destruct IH2 as (g'' & Hs2g'' & Hg''); eauto.
    - pose proof IHHsbs _ Hg as IH; clear IHHsbs.
      destruct IH as (g' & Hsg' & Hg'); eauto.
    - pose proof IHHsbs _ Hg as IH; clear IHHsbs.
      destruct IH as (g' & Hsg' & Hg').
      exists !{ g2 ≪ g' }!; split; auto.
      erewrite Env.shadow_eq_env_l; eauto.
    - pose proof IHHsbs _ Hg as IH; clear IHHsbs.
      destruct IH as (g' & Hsg' & Hg').
      exists !{ g2 ≪ g' }!; split; auto.
      erewrite Env.shadow_eq_env_l; eauto.
    - exists !{ x ↦ v;; g2}!; split; auto.
      constructor; destruct eo as [t | e]; eauto 2.
    - exists (lv_update lv v g2); split; try rewrite <- H; eauto.
    - econstructor; split; eauto 1.
      constructor; eauto.
    - pose proof IHHsbs _ Hg as IH; clear IHHsbs.
      destruct IH as (g' & Hs & Hg'); eauto.
    - pose proof IHHsbs _ Hg as IH; clear IHHsbs.
      destruct IH as (g' & Hs & Hg'); eauto.
    - 
  Admitted.
End EnvEq.

Section Proper.
  Context {tags_t : Type}.
    
  Global Instance Proper_expr_big_step :
    @Proper
      (epsilon -> Expr.e tags_t -> Val.v -> Prop)
      (Env.eq_env
         ==> ExprEquivalence.equive
         ==>  eq ==> fun (x y : Prop) => x -> y)
      expr_big_step.
  Proof.
    unfold Proper. intros a b c d e. cbv.
  Admitted.
End Proper.
