From Coq Require Import PArith.BinPos
     NArith.BinNat ZArith.BinInt.
From Poulet4.P4cub.Semantics Require Import Static.Static
     Dynamic.BigStep.Value.Typing
     Dynamic.BigStep.Value.Syntax
     Dynamic.BigStep.Value.IndPrincip.
From Poulet4 Require Import P4cub.Syntax.AST
  P4cub.Syntax.CubNotations Utils.ForallMap.
Import String.

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

Local Open Scope val_scope.
Local Open Scope type_scope.

(** Intial/Default val from a type. *)
Fixpoint val_of_typ (τ : Typ.t) : option Val.t :=
  match τ with
  | Typ.Error => Some $ Val.Error "no error"%string
  | Typ.Bool  => Some $ Val.Bool false
  | Typ.Bit w => Some $ w VW 0%Z
  | Typ.Int w => Some $ w VS 0%Z
  | Typ.VarBit w => Some $ Val.VarBit w w 0%Z
  | Typ.Array n t =>
      val_of_typ
        t >>| (fun v => repeat v $ N.to_nat n)
        >>| Val.Lists $ Lst.Array t
  | Typ.Struct b ts
    => sequence
        $ List.map val_of_typ ts
        >>| Val.Lists
        (if b then Lst.Header false else Lst.Struct)
  | Typ.Var _ => None
  end.

Lemma val_of_typ_ok : forall τ, typ_ok 0 τ -> exists V, val_of_typ τ = Some V.
Proof.
  intros t h; remember 0%nat as z eqn:eqz.
  induction h using custom_typ_ok_ind; subst; unravel; eauto; try lia.
  - pose proof IHh eq_refl as [v hv].
    exists (Val.Lists (Lst.Array t) (repeat v (N.to_nat n)));
      cbn. rewrite hv; reflexivity.
  - rewrite Forall_forall in H0.
    pose proof (fun t hin => H0 t hin eq_refl) as ih; clear H0.
    rewrite <- Forall_forall in ih.
    rewrite Forall_exists_factor in ih.
    destruct ih as [vs ih].
    rewrite Forall2_map_l with
      (f:=val_of_typ) (R:=fun ov V => ov = Some V),
        Forall2_sequence_iff in ih.
    rewrite ih; eauto.
Qed.

Local Open Scope pat_scope.

Fixpoint match_pattern (p : Pat.t) (V : Val.t) : bool :=
  match p, V with
  | Pat.Wild, _ => true
  | Pat.Mask (w PW a) (_ PW b), _ VW c
    => (Z.land a b =? Z.land c b)%Z
  | Pat.Range (w PW a) (_ PW b), _ VW c
    => (a <=? c)%Z && (c <=? b)%Z
  | w1 PW n1, w2 VW n2
    => (w1 =? w2)%N && (n1 =? n2)%Z
  | w1 PS n1, w2 VS n2
    => (w1 =? w2)%positive && (n1 =? n2)%Z
  | Pat.Lists ps, Val.Lists Lst.Struct vs =>
    (fix F ps vs :=
       match ps, vs with
       | [], [] => true
       | p::ps, v::vs => match_pattern p v && F ps vs
       | _, _ => false
       end) ps vs
  | _,_ => false
  end.

Fixpoint typ_of_val (V : Val.t) : Typ.t :=
  match V with
  | Val.Bool _ => Typ.Bool
  | w VW _ => Typ.Bit w
  | w VS _ => Typ.Int w
  | Val.VarBit m _ _ => Typ.VarBit m
  | Val.Error _ => Typ.Error
  | Val.Lists (Lst.Array τ) vs  =>
      Typ.Array (N.of_nat $ List.length vs) τ
  | Val.Lists Lst.Struct vs     =>
      Typ.Struct false (List.map typ_of_val vs)
  | Val.Lists (Lst.Header _) vs =>
      Typ.Struct true (List.map typ_of_val vs)
  end.

Lemma typ_of_val_of_typ : forall V τ,
    val_of_typ τ = Some V -> typ_of_val V = τ.
Proof.
  intro V; induction V using custom_val_ind;
    intros [] h; unravel in *;
    try match_some_inv; try some_inv;
    try (discriminate || reflexivity).
  f_equal.
  - match_some_inv; some_inv.
    rewrite repeat_length; lia.
  - pose proof Option.sequence_length _ _ Heqo as Hlen.
    rewrite map_length in Hlen.
    pose proof Forall_specialize_Forall2
         _ _ _ _ H _ (eq_sym Hlen) as h.
    rewrite <- Forall2_sequence_iff,
      sublist.Forall2_map1,Forall2_flip in Heqo.
    pose proof Forall2_impl _ _ _ _ _ _ h Heqo as h'.
    rewrite Forall2_map_l,Forall2_eq in h'; subst.
    destruct isheader; reflexivity.
Qed.

Lemma typ_of_val_of_typ_ok : forall τ,
    typ_ok 0 τ ->
    option_map typ_of_val (val_of_typ τ) = Some τ.
Proof.
  intros t h.
  destruct (val_of_typ_ok _ h) as [v hv].
  rewrite hv; cbn; f_equal.
  auto using typ_of_val_of_typ.
Qed.

Local Open Scope exp_scope.

Fixpoint exp_of_val (V : Val.t) : Exp.t :=
  match V with
  | Val.Bool b => Exp.Bool b
  | w VW n => w `W n
  | w VS z => w `S z
  | Val.VarBit m w n => Exp.VarBit m w n
  | Val.Error err => Exp.Error err
  | Val.Lists ls vs => Exp.Lists ls (map exp_of_val vs)
  end.

Lemma typ_of_exp_of_val : forall V,
    typ_of_exp (exp_of_val V) = typ_of_val V.
Proof.
  intro V; induction V using custom_val_ind;
    unravel; try reflexivity; f_equal.
  apply map_ext_Forall in H.
  rewrite map_map, map_length, H; reflexivity.
Qed.

Section Lemmas.
  Local Hint Resolve BitArith.bound0 : core.
  Local Hint Resolve IntArith.bound0 : core.
  Local Hint Constructors type_val : core.
  Local Hint Rewrite repeat_length.
  Local Hint Rewrite Pos2Nat.id : core.
  Local Hint Constructors type_lst_ok : core.
  Local Hint Constructors typ_ok_lists : core.
  
  Lemma val_of_typ_types : forall τ V,
      val_of_typ τ = Some V ->
      ⊢ᵥ V ∈ τ.
  Proof.
    intro t; induction t using custom_typ_ind;
      intros V h; unravel in *; try discriminate;
      try match_some_inv; try some_inv; auto.
    - eauto using N.le_refl.
    - match_some_inv; some_inv.
      econstructor; eauto using Forall2_repeat_both.
    - rewrite <- Forall2_sequence_iff, sublist.Forall2_map1 in Heqo.
      apply Forall2_length in Heqo as hlen.
      pose proof Forall_specialize_Forall2
           _ _ _ _ H _ hlen as h.
      rewrite Forall2_flip in Heqo,h.
      pose proof Forall2_impl
           _ _ _ _ _ _ h Heqo as h'.
      econstructor; destruct b; eauto.
  Qed.

  Lemma typ_of_val_typing : forall V τ,
      ⊢ᵥ V ∈ τ -> typ_of_val V = τ.
  Proof.
    intros V t h;
      induction h using custom_type_val_ind;
      unravel in *; try reflexivity.
    rewrite Forall2_map_l, Forall2_eq in H1; subst.
    inv H; try reflexivity.
    apply f_equal with (f := @List.length Typ.t) in H4.
    rewrite repeat_length,map_length in H4.
    rewrite <- H4; f_equal; lia.
  Qed.
  
  Local Hint Constructors type_exp : core.
  Local Hint Constructors relop : core.
  Local Hint Resolve typ_of_val_typing : core.
  Hint Rewrite map_length : core.
  
  Lemma exp_of_val_types : forall V τ,
      typ_ok 0 τ ->
      ⊢ᵥ V ∈ τ ->
      `⟨ 0, [] ⟩ ⊢ exp_of_val V ∈ τ.
  Proof.
    intros V t hok h;
      induction h using custom_type_val_ind;
      unravel; auto.
    econstructor; eauto; cbn in *.
    - inv H; inv hok; auto.
    - assert (hokts : Forall (typ_ok 0) ts).
      { inv H; inv hok; eauto using sublist.Forall_repeat. }
      rewrite sublist.Forall2_map1.
      eapply Forall2_impl with (R := fun v t => typ_ok 0 t) in H1; eauto.
      apply Forall_Forall2_only_r; eauto using Forall2_length.
  Qed.
End Lemmas.

Local Close Scope val_scope.
Local Close Scope type_scope.
Local Close Scope pat_scope.
Local Close Scope exp_scope.
