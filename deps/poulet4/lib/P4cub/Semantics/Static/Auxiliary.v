From Poulet4 Require Export
     P4cub.Semantics.Static.Typing
     P4cub.Semantics.Static.IndPrincip
     P4cub.Semantics.Static.Util
     Utils.ForallMap.

Local Hint Constructors t_ok : core.
  
Lemma type_expr_t_ok : forall Γ e τ,
    Γ ⊢ₑ e ∈ τ ->
    Forall (t_ok (type_vars Γ)) (types Γ) ->
    t_ok (type_vars Γ) τ.
Proof.
  intros G e t het hok;
    induction het using custom_type_expr_ind; auto.
  apply Forall2_only_r_Forall in H2.
  rewrite Forall_forall in H2.
  pose proof (fun t hin => H2 t hin hok) as h; clear H2.
  rewrite <- Forall_forall in h.
  inv H; inv H0; auto.
Qed.
