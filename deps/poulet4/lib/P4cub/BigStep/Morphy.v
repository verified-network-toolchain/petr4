Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.Syntax.Syntax Poulet4.P4cub.Envn
        Poulet4.P4cub.BigStep.Value.Syntax
        Poulet4.P4cub.BigStep.Semantics
        Poulet4.P4cub.BigStep.IndPrincip
        Coq.Classes.Morphisms.
Import AllCubNotations Val.ValueNotations
       Val.LValueNotations F.FieldTactics Step
       Poulet4.P4cub.BigStep.IndPrincip.

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

  Local Hint Resolve eq_env_copy_in : core.
  
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

  Local Hint Resolve eq_env_copy_out_l : core.
  
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

  Local Hint Resolve eq_env_copy_out_r : core.
  
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

  Lemma eq_env_param_arg_eval :
    forall (args : Expr.args tags_t) argsv ϵ ϵ',
      ϵ ≝ ϵ' ->
      F.relfs
        (rel_paramarg
           (fun e v => ⟨ ϵ, e ⟩ ⇓ v)
           (fun e lv => ⧠ e ⇓ lv))
        args argsv ->
      F.relfs
        (rel_paramarg
           (fun e v => ⟨ ϵ', e ⟩ ⇓ v)
           (fun e lv => ⧠ e ⇓ lv)) args argsv.
  Proof.
    intros args argsv h h' Hh Hargs.
    autounfold with * in *; unravel in *; autorewrite with core in *.
    destruct Hargs as [Hxs Hargs]; split; auto; clear Hxs.
    rewrite Utils.Forall2_map_both in *.
    unfold F.f in *;
      remember (map snd args) as args' eqn:Heqargs;
      remember (map snd argsv) as argsv' eqn:Heqargsv;
      clear args argsv Heqargs Heqargsv.
    induction Hargs as
        [| [e | e | e | e] [v | lv | lv | v] es vs Hev IHevs];
      unfold rel_paramarg in *;
      unravel in *; constructor; eauto.
  Qed.

  Local Hint Resolve eq_env_param_arg_eval : core.
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

  Local Hint Resolve eq_env_parser_expr_big_step : core.
  Local Hint Constructors stmt_big_step : core.
  Local Hint Constructors bigstep_state_machine : core.
  Local Hint Constructors bigstep_state_block : core.
  Local Hint Resolve Env.shadow_eq_env_l : core.
  Local Hint Resolve Env.shadow_eq_env_r : core.
  
  Definition
    eq_env_stmt_big_step_def
    pkt fs ϵ₁ cx (s : Stmt.s tags_t) ϵ₁' sig pkt'
    (H : ⟪ pkt, fs, ϵ₁, cx, s ⟫ ⤋ ⟪ ϵ₁', sig, pkt' ⟫) := forall ϵ₂,
      ϵ₁ ≝ ϵ₂ -> exists ϵ₂',
        ⟪ pkt , fs , ϵ₂ , cx , s ⟫ ⤋ ⟪ ϵ₂' , sig , pkt' ⟫
        /\ ϵ₁' ≝ ϵ₂'.
  
  Definition
    eq_env_big_step_state_machine_def
    pkt fs ϵ₁ ps ee (sb : AST.Parser.state_block tags_t)
    states strt_lbl ϵ₁' nxt_lbl pkt'
    (H : SM (pkt, fs, ϵ₁, ps, ee, sb, states, strt_lbl)
            ⇝ ⟨ ϵ₁', nxt_lbl, pkt' ⟩) := forall ϵ₂,
      ϵ₁ ≝ ϵ₂ -> exists ϵ₂',
        SM (pkt, fs, ϵ₂, ps, ee, sb, states, strt_lbl)
           ⇝ ⟨ ϵ₂', nxt_lbl, pkt' ⟩ /\ ϵ₁' ≝ ϵ₂'.

  Definition
    eq_env_big_step_state_block_def
    pkt fs ϵ₁ ps ee (sb : AST.Parser.state_block tags_t)
    ϵ₁' lbl pkt'
    (H : SB (pkt, fs, ϵ₁, ps, ee, sb)⇝ ⟨ ϵ₁', lbl, pkt' ⟩) := forall ϵ₂,
      ϵ₁ ≝ ϵ₂ -> exists ϵ₂',
        SB (pkt, fs, ϵ₂, ps, ee, sb)⇝
           ⟨ ϵ₂', lbl, pkt' ⟩ /\ ϵ₁' ≝ ϵ₂'.

  Definition eq_env_sbs_ind :=
    stmt_big_step_ind
      _ eq_env_stmt_big_step_def
      eq_env_big_step_state_machine_def
      eq_env_big_step_state_block_def.
  
  Definition eq_env_bsm_ind :=
    bigstep_state_machine_ind
      _ eq_env_stmt_big_step_def
      eq_env_big_step_state_machine_def
      eq_env_big_step_state_block_def.

  Definition eq_env_bsb_ind :=
    bigstep_state_block_ind
      _ eq_env_stmt_big_step_def
      eq_env_big_step_state_machine_def
      eq_env_big_step_state_block_def.

  Ltac plz_have_mercy :=
    match goal with
    | IH: (forall h', ?h ≝ h' -> exists h'', _ /\ _ ≝ h''), H: ?h ≝ _
      |- _ => pose proof H as ? ;
            apply IH in H as (? & ? & ?); clear IH
    end.

  Ltac copyin_mercy :=
    match goal with
    | IH : (forall eps,
               copy_in ?vs ?h ?cls ≝ eps ->
               exists eps', _ /\ _ ≝ eps'), Heps: ?h ≝ ?h' |- _
      => assert (Hcpyin : copy_in vs h cls = copy_in vs h' cls) by eauto;
        assert (Hcpyin_eq_env : copy_in vs h cls ≝ copy_in vs h' cls)
          by (rewrite Hcpyin; reflexivity)
    end.

  Ltac block_mercy :=
    match goal with
    | H: ?h1 ≝ ?h2, H': ?h1' ≝ ?h2'
      |- exists h, _ /\ !{ ?h1 ≪ ?h1' }! ≝ h
      => exists !{ h2 ≪ h2' }!; split; auto;
        erewrite Env.shadow_eq_env_l; eauto;
        assumption
    end.
  
  Lemma eq_env_stmt_big_step :
    forall pkt fs ϵ₁ cx (s : Stmt.s tags_t) ϵ₁' sig pkt'
      (H : ⟪ pkt, fs, ϵ₁, cx, s ⟫ ⤋ ⟪ ϵ₁', sig, pkt' ⟫),
      eq_env_stmt_big_step_def _ _ _ _ _ _ _ _ H.
  Proof.
    apply eq_env_sbs_ind;
      unfold eq_env_stmt_big_step_def,
      eq_env_big_step_state_machine_def,
      eq_env_big_step_state_block_def;
      intros; subst; try copyin_mercy;
        repeat plz_have_mercy;
        try block_mercy; eauto 7.
    - exists !{ x ↦ v;; ϵ₂}!; split; auto.
      constructor; destruct eo as [t | e]; eauto 2.
    - (* TODO: table invocation semantics... *) admit.
    - erewrite eq_env_copy_in in e1 by eauto.
      exists (copy_out argsv cls'' ϵ₂). eauto.
  Admitted.

  Lemma eq_env_big_step_state_machine :
    forall pkt fs ϵ₁ ps ee sb states strt_lbl ϵ₁' nxt_lbl pkt'
      (H : SM (pkt, fs, ϵ₁, ps, ee, sb, states, strt_lbl)
              ⇝ ⟨ ϵ₁', nxt_lbl, pkt' ⟩),
      eq_env_big_step_state_machine_def _ _ _ _ _ _ _ _ _ _ _ H.
  Proof.
    apply eq_env_bsm_ind;
      unfold eq_env_stmt_big_step_def,
      eq_env_big_step_state_machine_def,
      eq_env_big_step_state_block_def;
      intros; subst; try copyin_mercy;
        repeat plz_have_mercy;
        try block_mercy; eauto 7.
    - exists !{ x ↦ v;; ϵ₂}!; split; auto.
      constructor; destruct eo as [t | e]; eauto 2.
    - (* TODO: table invocation semantics... *) admit.
    - erewrite eq_env_copy_in in e1 by eauto.
      exists (copy_out argsv cls'' ϵ₂). eauto.
  Admitted.

  Lemma eq_env_big_step_state_block :
    forall pkt fs ϵ₁ ps ee sb ϵ₁' lbl pkt'
      (H : SB (pkt, fs, ϵ₁, ps, ee, sb)⇝ ⟨ ϵ₁', lbl, pkt' ⟩),
      eq_env_big_step_state_block_def _ _ _ _ _ _ _ _ _ H.
  Proof.
    apply eq_env_bsb_ind;
      unfold eq_env_stmt_big_step_def,
      eq_env_big_step_state_machine_def,
      eq_env_big_step_state_block_def;
      intros; subst; try copyin_mercy;
        repeat plz_have_mercy;
        try block_mercy; eauto 7.
    - exists !{ x ↦ v;; ϵ₂}!; split; auto.
      constructor; destruct eo as [t | e]; eauto 2.
    - (* TODO: table invocation semantics... *) admit.
    - erewrite eq_env_copy_in in e1 by eauto.
      exists (copy_out argsv cls'' ϵ₂). eauto.
  Admitted.
End EnvEq.

Section Proper.
  Context {tags_t : Type}.

  Global Instance Proper_expr_big_step_env :
    @Proper
      (epsilon -> Expr.e tags_t -> Val.v -> Prop)
      (Env.eq_env ==> eq ==> eq ==> fun (P Q : Prop) => P -> Q)
      expr_big_step.
  Proof.
    intros eps eps' Heps e e' He v v' Hv Hev; subst.
    eauto using eq_env_expr_big_step.
  Qed.
    
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

  Global Instance Proper_stmt_big_step_env :
    @Proper
      (Paquet.t -> fenv -> epsilon -> ctx -> Stmt.s tags_t ->
       epsilon -> signal -> Paquet.t -> Prop)
      (eq ==> eq ==> Env.eq_env ==> eq ==> eq ==>
          Env.eq_env ==> eq ==> eq ==> fun (P Q : Prop) => P -> Q)
      stmt_big_step.
  Proof.
    intros
      ? pkt Hpt ? fs Hfs eps1 eps2 Heps ? cx Hcx ? s Hs
      eps1' eps2' Heps' ? sg Hsg ? pkt' Hpkt' H; subst.
    pose proof eq_env_stmt_big_step _ _ _ _ _ _ _ _ H as H'.
    unfold eq_env_stmt_big_step_def in H'.
    pose proof H' _ Heps as H''; clear H'.
    destruct H'' as (h' & Hsh' & Hh').
    (* Maybe env should be a function again... *)
  Admitted.
End Proper.
