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
  constructor.
  apply Forall2_only_r_Forall in H1.
  rewrite Forall_forall in H1.
  pose proof (fun t hin => H1 t hin hok) as h; clear H1.
  rewrite <- Forall_forall in h; assumption.
Qed.
