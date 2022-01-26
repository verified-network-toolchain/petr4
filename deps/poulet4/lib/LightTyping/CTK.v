Require Import Poulet4.Ops Poulet4.Maps
        Poulet4.Typed Poulet4.Value
        Poulet4.Syntax Poulet4.Semantics
        Poulet4.Monads.Monad Poulet4.Monads.Option
        Poulet4.SyntaxUtil Poulet4.LightTyping.Utility.

Notation path := (list String.string).

(** * Compile-time Known Evaluation. *)

Reserved Notation "'⟨' p ',' Σ ',' e '⟩' '⇝' v" (at level 80, no associativity).

Inductive CTK_eval
          {tags_t : Type}
          (p : path)
          (Σ : genv_const)
  : @Expression tags_t -> @ValueBase bool -> Prop :=
| CTK_bool i b τ d :
    ⟨ p, Σ, MkExpression i (ExpBool b) τ d ⟩ ⇝ ValBaseBool b
| CTK_num i n τ d :
    ⟨ p, Σ, MkExpression i (ExpInt n) τ d ⟩ ⇝ eval_p4int_val n
| CTK_const i x l τ v :
    loc_to_val_const Σ p l = Some v ->
    ⟨ p, Σ, MkExpression i (ExpName x l) τ Directionless ⟩ ⇝ v
| CTK_uop i op e τ d v v' :
    eval_unary_op op v = Some v' ->
    ⟨ p, Σ, e ⟩ ⇝ v ->
    ⟨ p, Σ, MkExpression i (ExpUnaryOp op e) τ d ⟩ ⇝ v'
| CTK_bop i op e₁ e₂ τ d v v₁ v₂ :
    eval_binary_op op v₁ v₂ = Some v ->
    ⟨ p, Σ, e₁ ⟩ ⇝ v₁ ->
    ⟨ p, Σ, e₂ ⟩ ⇝ v₂ ->
    ⟨ p, Σ, MkExpression i (ExpBinaryOp op (e₁,e₂)) τ d ⟩ ⇝ v
where "'⟨' p ',' Σ ',' e '⟩' '⇝' v" := (CTK_eval p Σ e v) : type_scope.

Section CTKEval.
  Context {tags_t: Type}.
  Notation expr := (@Expression tags_t).
  Notation Val := (@ValueBase bool).

  Variables (p: path) (Σ: genv_const).

  Fixpoint ctk_eval (e: expr) : option Val :=
    match e with
    | MkExpression _ (ExpBool b) _ _ => mret (ValBaseBool b)
    | MkExpression _ (ExpInt  n) _ _ => mret (eval_p4int_val n)
    | MkExpression
        _ (ExpName _ l) _ Directionless => loc_to_val_const Σ p l
    | MkExpression _ (ExpUnaryOp o e) _ _
      => ctk_eval e >>= eval_unary_op o
    | MkExpression _ (ExpBinaryOp o (e₁,e₂)) _ _
      => let* v₁ := ctk_eval e₁ in
        let* v₂ := ctk_eval e₂ in
        eval_binary_op o v₁ v₂
    | _ => None
    end.

  Local Hint Unfold option_bind : core.
  
  Lemma ctk_eval_complete : forall e v,
      ⟨ p, Σ, e ⟩ ⇝ v -> ctk_eval e = Some v.
  Proof.
    intros e v H; induction H;
      cbn in *; autounfold with core in *;
        repeat match goal with
               | H: ?trm = _ |- context [?trm]
                 => rewrite H; clear H
               end;
        try reflexivity; auto.
  Qed.

  Local Hint Constructors CTK_eval : core.
  
  Lemma ctk_eval_sound : forall e v,
      ctk_eval e = Some v -> ⟨ p, Σ, e ⟩ ⇝ v.
  Proof.
    intro e; induction e using expr_ind; intros v Hev;
      cbn in *; autounfold with core in *;
        try discriminate;
        repeat match_some_inv; try some_inv; eauto.
    - destruct dir; cbn in *; inv Hev; auto.
    - destruct args as [e₁ e₂]; cbn in *;
        repeat match_some_inv; eauto.
  Qed.

  Local Hint Constructors exec_expr : core.
  Local Hint Unfold eval_val_to_sval : core.
  Local Hint Unfold loc_to_sval_const : core.
  Local Hint Unfold option_map : core.
  Local Hint Resolve val_to_sval_ex : core.
  Local Hint Resolve sval_to_val_eval_val_to_sval : core.
  
  Lemma CTK_exec_expr :
    forall (T: Target) (gf: genv_func) (gt: genv_typ)
      (gs: genv_senum) (gi: genv_inst) (ee: extern_env)
      (rob : option bool -> bool -> Prop) (st : state)
      (e : expr) (v : ValueBase),
      (forall b, rob (Some b) b) ->
      ⟨p,Σ,e⟩ ⇝ v ->
      @exec_expr
        _ T
        {| ge_func:=gf; ge_typ:=gt; ge_senum:=gs;
           ge_inst:=gi; ge_const:=Σ; ge_ext:=ee |}
        rob p st e (ValueBaseMap Some v).
  Proof.
    intros T gf gt gs gi ee rob st e v Hrob H;
      induction H; cbn in *; eauto.
    - constructor; destruct n as [i' z [[w []] |]]; cbn; try reflexivity.
    - apply exec_expr_name_const; cbn; try reflexivity.
      autounfold with core; cbn.
      rewrite H; reflexivity.
  Qed.
End CTKEval.
