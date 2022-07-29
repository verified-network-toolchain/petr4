From Coq Require Import PArith.BinPos
     NArith.BinNat ZArith.BinInt.
From Poulet4.P4cub.Semantics Require Import Static.Static
     Dynamic.BigStep.Value.Typing
     Dynamic.BigStep.Value.Syntax
     Dynamic.BigStep.Value.IndPrincip.
Import String Val ValueNotations ExprNotations ParserNotations.
From Poulet4 Require Import P4cub.Syntax.AST
     P4cub.Syntax.CubNotations Utils.ForallMap.

(* TODO: Also in [P4light/Semantics/Typing/Utility.v]
   Should be moved to somewhere in [Utils]. *)
Ltac some_inv :=
  match goal with
  | H: Some _ = Some _ |- _ => inv H
  end.

Ltac match_some_inv :=
  match goal with
  | H: match ?trm with Some _ => _ | None => _ end = Some _
    |- _ => destruct trm as [? |] eqn:? ; cbn in *;
          try discriminate
  end.

Local Open Scope value_scope.
Local Open Scope type_scope.

(** Intial/Default value from a type. *)
Fixpoint v_of_t (τ : Expr.t) : option v :=
  match τ with
  | Expr.TError => Some $ Error "no error"%string
  | Expr.TBool  => Some $ Bool false
  | Expr.TBit w => Some $ Bit w 0%Z
  | Expr.TInt w => Some $ Int w 0%Z
  | Expr.TArray n t =>
      v_of_t
        t >>| (fun v => repeat v $ N.to_nat n)
        >>| Lists $ Expr.lists_array t
  | Expr.TStruct b ts
    => sequence
        $ List.map v_of_t ts
        >>| Lists
        (if b then Expr.lists_header false else Expr.lists_struct)
  | Expr.TVar _ => None
  end.

Lemma v_of_t_ok : forall τ, t_ok 0 τ -> exists V, v_of_t τ = Some V.
Proof.
  intros t h; remember 0%nat as z eqn:eqz.
  induction h using custom_t_ok_ind; subst; unravel; eauto; try lia.
  - pose proof IHh eq_refl as [v hv].
    exists (Lists (Expr.lists_array t) (repeat v (N.to_nat n)));
      cbn. rewrite hv; reflexivity.
  - rewrite Forall_forall in H0.
    pose proof (fun t hin => H0 t hin eq_refl) as ih; clear H0.
    rewrite <- Forall_forall in ih.
    rewrite Forall_exists_factor in ih.
    destruct ih as [vs ih].
    rewrite Forall2_map_l with
      (f:=v_of_t) (R:=fun ov V => ov = Some V),
        Forall2_sequence_iff in ih.
    rewrite ih; eauto.
Qed.

Local Open Scope pat_scope.

Fixpoint match_pattern (p : Parser.pat) (V : v) : bool :=
  match p, V with
  | Parser.Wild, _ => true
  | Parser.Mask (w PW a) (_ PW b), _ VW c
    => (Z.land a b =? Z.land c b)%Z
  | Parser.Range (w PW a) (_ PW b), _ VW c
    => (a <=? c)%Z && (c <=? b)%Z
  | w1 PW n1, w2 VW n2
    => (w1 =? w2)%N && (n1 =? n2)%Z
  | w1 PS n1, w2 VS n2
    => (w1 =? w2)%positive && (n1 =? n2)%Z
  | Parser.Lists ps, Lists Expr.lists_struct vs =>
    (fix F ps vs :=
       match ps, vs with
       | [], [] => true
       | p::ps, v::vs => match_pattern p v && F ps vs
       | _, _ => false
       end) ps vs
  | _,_ => false
  end.

Fixpoint t_of_v (V : v) : Expr.t :=
  match V with
  | Bool _ => Expr.TBool
  | w VW _ => Expr.TBit w
  | w VS _ => Expr.TInt w
  | Error _ => Expr.TError
  | Lists (Expr.lists_array τ) vs  =>
      Expr.TArray (N.of_nat $ List.length vs) τ
  | Lists Expr.lists_struct vs     =>
      Expr.TStruct false (List.map t_of_v vs)
  | Lists (Expr.lists_header _) vs =>
      Expr.TStruct true (List.map t_of_v vs)
  end.

Lemma t_of_v_of_t : forall V τ,
    v_of_t τ = Some V -> t_of_v V = τ.
Proof.
  intro V; induction V using custom_v_ind;
    intros [] h; unravel in *;
    try match_some_inv; try some_inv;
    try (discriminate || reflexivity).
  f_equal.
  - match_some_inv; some_inv.
    rewrite repeat_length; lia.
  - pose proof sequence_length _ _ Heqo as Hlen.
    rewrite map_length in Hlen.
    pose proof Forall_specialize_Forall2
         _ _ _ _ H _ (eq_sym Hlen) as h.
    rewrite <- Forall2_sequence_iff,
      sublist.Forall2_map1,Forall2_flip in Heqo.
    pose proof Forall2_impl _ _ _ _ _ _ h Heqo as h'.
    rewrite Forall2_map_l,Forall2_eq in h'; subst.
    destruct isheader; reflexivity.
Qed.

Lemma t_of_v_of_t_ok : forall τ,
    t_ok 0 τ ->
    option_map t_of_v (v_of_t τ) = Some τ.
Proof.
  intros t h.
  destruct (v_of_t_ok _ h) as [v hv].
  rewrite hv; cbn; f_equal.
  auto using t_of_v_of_t.
Qed.

Local Open Scope expr_scope.

Fixpoint e_of_v (V : v) : Expr.e :=
  match V with
  | Bool b => Expr.Bool b
  | w VW n => w `W n
  | w VS z => w `S z
  | Error err => Expr.Error err
  | Lists ls vs => Expr.Lists ls (map e_of_v vs)
  end.

Lemma t_of_e_of_v : forall V,
    t_of_e (e_of_v V) = t_of_v V.
Proof.
  intro V; induction V using custom_v_ind;
    unravel; try reflexivity; f_equal.
  - apply map_ext_Forall in H.
    rewrite map_map; assumption.
Qed.

Section Lemmas.
  Local Hint Resolve BitArith.bound0 : core.
  Local Hint Resolve IntArith.bound0 : core.
  Local Hint Constructors type_value : core.
  Hint Rewrite repeat_length.
  Hint Rewrite Pos2Nat.id : core.
  
  Lemma v_of_t_types : forall τ V,
      v_of_t τ = Some V ->
      ⊢ᵥ V ∈ τ.
  Proof.
    intro t; induction t using custom_t_ind;
      intros V h; unravel in *; try discriminate;
      try match_some_inv; try some_inv; auto.
    constructor.
    - elim b; trivial.
    - generalize dependent l.
      induction H as [| t ts ht hts ihts];
        intros vs h; unravel in *;
        repeat match_some_inv; some_inv; auto.
  Qed.

  Lemma t_of_v_typing : forall V τ,
      ⊢ᵥ V ∈ τ -> t_of_v V = τ.
  Proof.
    intros V t h;
      induction h using custom_type_value_ind;
      unravel in *; try reflexivity.
    f_equal.
    - rewrite Forall2_map_l,
        Forall2_eq in H1; assumption.
    - destruct ob as [[|] |]; destruct b;
        reflexivity || contradiction.
  Qed.
  
  Local Hint Constructors type_expr : core.
  Local Hint Constructors relop : core.
  Local Hint Resolve t_of_v_typing : core.
  Hint Rewrite map_length : core.
  
  Lemma expr_of_value_types : forall V τ,
      ⊢ᵥ V ∈ τ ->
      {|type_vars:=0;types:=[]|} ⊢ₑ e_of_v V ∈ τ.
  Proof.
    intros V t h;
      induction h using custom_type_value_ind;
      unravel; auto.
    constructor.
    - destruct ob; destruct b;
        unravel; try contradiction; auto.
    - rewrite Forall2_map_l in H1; assumption.
  Qed.
End Lemmas.

Local Close Scope value_scope.
Local Close Scope type_scope.
Local Close Scope pat_scope.
Local Close Scope expr_scope.
