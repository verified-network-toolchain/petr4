Set Warnings "-custom-entry-overridden".
Require Export Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Transformations.Statementize.
Require Export Poulet4.P4cub.BigStep.BigStep
        Poulet4.P4cub.Envn.
Import AllCubNotations Env.EnvNotations
       Val.ValueNotations Step.

Section Correct.
  Context {tags_t : Type}.

  (* Type Soundness for statements
     would be useful for this.
     Knowing [exists] an environment for
     the statement to evaluate to
     (worry about this later). *)
  Lemma expr_semantic_pres : forall (e e' : Expr.e tags_t) env env' s,
      TransformExpr e env = (s, e', env') ->
      forall ϵ v pkt fe ctx, (* ctx & fe shouldn't matter. *)
        ⟨ ϵ, e ⟩ ⇓ v ->
        exists ϵ',
          ⟪ pkt , fe , ϵ , ctx , s ⟫ ⤋ ⟪ ϵ' , C , pkt ⟫ /\
          (* packet [pkt] shouldn't change in stmt evalution. *)
          ⟨ ϵ', e' ⟩ ⇓ v (*/\ ϵ ⊆ ϵ' (define sub-env relation) *).
  Proof.
    (* TODO. *)
  Abort.
End Correct.
