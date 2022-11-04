From Poulet4 Require Import P4cub.Syntax.Syntax
     P4cub.Semantics.Climate Utils.ForallMap.
From Poulet4.P4cub.Semantics.Dynamic Require Import
     BigStep.Value.Syntax BigStep.Semantics BigStep.IndPrincip
     BigStep.Value.Typing.
Import AllCubNotations Val.ValueNotations
       Val.LValueNotations.

Section Properties.  
  Local Hint Resolve ForallMap.Forall2_dumb : core.
  Local Hint Constructors expr_big_step : core.
  Local Hint Constructors stmt_big_step : core.
  Local Hint Resolve lv_update_length : core.
  Local Hint Rewrite lv_update_length : core.

  Lemma lv_update_signal_length : forall olv sig ϵ,
      length (lv_update_signal olv sig ϵ) = length ϵ.
  Proof.
    intros [] [| | | | []] ϵ; cbn; auto.
  Qed.

  Local Hint Resolve lv_update_signal_length : core.
  Local Hint Rewrite lv_update_signal_length : core.
  
  Lemma copy_out_from_args_length : forall vs₁ vs₂ ϵ,
      length (copy_out_from_args vs₁ vs₂ ϵ) = length ϵ.
  Proof.
    intro vs1; induction vs1 as [| [] vs1 ih];
      intros [| [] vs2] ϵ; cbn in *;
      try rewrite ih; auto.
  Qed.

  Local Hint Resolve copy_out_length : core.
  Local Hint Rewrite copy_out_length : core.
  Local Hint Resolve copy_out_from_args_length : core.
  Local Hint Rewrite copy_out_from_args_length : core.
  
  Context `{ext_sem : Extern_Sem}.

  Local Hint Rewrite app_length : core.
  
  Lemma sbs_length : forall Ψ ϵ ϵ' c s sig ψ,
      ⧼ Ψ, ϵ, c, s ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽ -> length ϵ = length ϵ'.
  Proof.
    intros Ψ ϵ ϵ' c s sig ψ h;
      induction h; autorewrite with core in *; auto; lia.
  Qed.
End Properties.
