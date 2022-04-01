Require Import Coq.NArith.BinNat
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Syntax
        Coq.PArith.BinPos Coq.ZArith.BinInt
        Poulet4.P4cub.Syntax.CubNotations
        Poulet4.P4cub.Semantics.Static.Util
        Poulet4.P4cub.Semantics.Static.IndPrincip
        Poulet4.Utils.ForallMap
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.IndPrincip
        (*Poulet4.P4cub.Syntax.IndPrincip*).
Import Val ValueNotations ExprNotations ParserNotations.

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
  | Expr.TError => Some $ Error None
  | Expr.TBool  => Some $ Bool false
  | Expr.TBit w => Some $ Bit w 0%Z
  | Expr.TInt w => Some $ Int w 0%Z
  | Expr.TStruct ts b
    => let^ vs := sequence $ List.map v_of_t ts in
      Struct vs (if b then Some false else None)
  | Expr.TVar _ => None
  end.

Lemma v_of_t_ok : forall τ, t_ok 0 τ -> exists V, v_of_t τ = Some V.
Proof.
  intros t h; remember 0%nat as z eqn:eqz.
  induction h using custom_t_ok_ind; subst; unravel; eauto; try lia.
  rewrite Forall_forall in H0.
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
  | w1 PW n1, w2 VW n2 =>
    (w1 =? w2)%N && (n1 =? n2)%Z
  | w1 PS n1, w2 VS n2 =>
    (w1 =? w2)%N && (n1 =? n2)%Z
  | Parser.Struct ps, Struct vs None =>
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
  | Struct vs ob
    => Expr.TStruct (List.map t_of_v vs) (if ob then true else false)
  end.

Lemma t_of_v_of_t : forall V τ,
    v_of_t τ = Some V -> t_of_v V = τ.
Proof.
  intro V; induction V using custom_v_ind;
    intros [] h; unravel in *;
    try match_some_inv; try some_inv;
    try (discriminate || reflexivity).
  f_equal.
  - generalize dependent fields.
    clear isheader.
    induction H as [| V vs h ih];
      intros [| t ts] hs; cbn in *;
      try (discriminate || reflexivity);
      unfold option_bind in hs;
      repeat match_some_inv. some_inv.
    f_equal; auto.
  - destruct isheader; reflexivity.
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
  | Struct vs ob
    => Expr.Struct (map e_of_v vs) (option_map Expr.Bool ob)
  end.

Lemma t_of_e_of_v : forall V,
    t_of_e (e_of_v V) = t_of_v V.
Proof.
  intro V; induction V using custom_v_ind;
    unravel; try reflexivity; f_equal.
  - apply map_ext_Forall in H.
    rewrite map_map; assumption.
  - destruct ob; reflexivity.
Qed.

Local Close Scope value_scope.
Local Close Scope type_scope.
Local Close Scope pat_scope.
Local Close Scope expr_scope.
