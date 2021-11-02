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
  
  Lemma stmt_big_step_sub_env :
    forall ϵ ϵ' (s : Stmt.s tags_t) pkt pkt' fs cx sig,
      ⟪ pkt , fs , ϵ , cx , s ⟫ ⤋ ⟪ ϵ' , sig , pkt' ⟫ -> ϵ ⊆ ϵ'.
  Proof.
    intros ? ? ? ? ? ? ? ? Hevals; induction Hevals;
      try reflexivity;
      try match goal with
          | H12: ?e1 ⊆ ?e2, H23: ?e2 ⊆ ?e3
            |- ?e1 ⊆ ?e3 => transitivity e2; assumption
          end; auto.
    - (* not generally true. *)
  Abort.
End Properties.
