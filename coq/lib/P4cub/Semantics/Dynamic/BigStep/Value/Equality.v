Require Import Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Syntax
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.IndPrincip
        Poulet4.P4cub.Syntax.Equality Coq.ZArith.BinInt Coq.NArith.BinNat.

(** Computational Value equality *)
Fixpoint eqb_val (v1 v2 : Val.t) : bool :=
  let fix lstruct (vs1 vs2 : list Val.t) : bool :=
    match vs1, vs2 with
    | [], [] => true
    | v1::vs1, v2::vs2 => eqb_val v1 v2 && lstruct vs1 vs2
    | [], _::_ | _::_, [] => false
    end in
  match v1, v2 with
  | Val.Bool b1, Val.Bool b2 => eqb b1 b2
  | Val.Int w1 n1, Val.Int w2 n2 => (w1 =? w2)%positive && (n1 =? n2)%Z
  | Val.Bit w1 n1, Val.Bit w2 n2 => (w1 =? w2)%N && (n1 =? n2)%Z
  | Val.VarBit m1 w1 n1, Val.VarBit m2 w2 n2 => (m1 =? m2)%N && (w1 =? w2)%N && (n1 =? n2)%Z
  | Val.Error err1, Val.Error err2
    => if equiv_dec err1 err2 then true else false
  | Val.Lists ls1 vs1, Val.Lists ls2 vs2
    => lists_eqb ls1 ls2 && lstruct vs1 vs2
  | _,          _          => false
  end.

Local Hint Rewrite eqb_reflx.
Local Hint Rewrite equiv_dec_refl.
Local Hint Rewrite Pos.eqb_refl.
Local Hint Rewrite Z.eqb_refl.
Local Hint Rewrite N.eqb_refl.
Local Hint Rewrite andb_true_r.
Local Hint Rewrite lists_eqb_refl.
Local Hint Resolve lists_eqb_eq : core.
Local Hint Extern 0 => equiv_dec_refl_tactic : core.

Lemma eqb_val_refl : forall V : Val.t, eqb_val V V = true.
Proof.
  induction V using custom_val_ind; simpl in *;
    autorewrite with core; simpl; auto;
    try ind_list_Forall;
    intuition; autorewrite with core; simpl;
    repeat (rewrite_true; simpl); auto.
Qed.

Ltac eq_true_terms :=
  match goal with
  | H: eqb _ _ = true |- _
    => apply eqb_prop in H; subst
  | H: (_ =? _)%N = true |- _
    => apply N.eqb_eq in H; subst
  | H: (_ =? _)%positive = true |- _
    => apply Pos.eqb_eq in H; subst
  | H: (_ =? _)%Z = true |- _
    => apply Z.eqb_eq in H; subst
  | H: context [equiv_dec ?x1 ?x2 &&&& _] |- _
    => destruct (equiv_dec x1 x2) as [? | ?];
      simpl in H; try discriminate
  | H: context [if equiv_dec ?t1 ?t2 then _ else _] |- _
    => destruct (equiv_dec t1 t2) as [? | ?];
      simpl in H; try discriminate
  | H: relop _ _ _ |- _ => inv H
  end.
  
Ltac eauto_too_dumb :=
  match goal with
  | H: ?f ?x ?y = ?z,
      IH: (forall y, ?f ?x y = ?z -> _)
    |- _ => apply IH in H; clear IH
  end.
  
Lemma eqb_val_eq : forall v1 v2 : Val.t, eqb_val v1 v2 = true -> v1 = v2.
Proof.
  induction v1 using custom_val_ind; intros []; intros;
    simpl in *; try discriminate;
    repeat destruct_andb;
    repeat (eq_true_terms); unfold equiv in *; auto; f_equal;
    repeat (eq_true_terms); auto;
    try match goal with
        | IH: Forall _ ?vs1,
            H: _ ?vs1 ?vs2 = true
          |- ?vs1 = ?vs2
          => generalize dependent vs2;
            induction vs1; intros []; intros;
            try discriminate; try inv_Forall_cons;
            repeat destruct_andb; intuition;
            repeat eauto_too_dumb; subst; auto
        end.
Qed.

Local Hint Resolve eqb_val_refl : core.
Local Hint Resolve eqb_val_eq : core.

Lemma eqb_val_eq_iff : forall v1 v2 : Val.t, eqb_val v1 v2 = true <-> v1 = v2.
Proof.
  intros; split; intros; subst; auto.
Qed.

Local Hint Resolve eqb_val_eq_iff : core.

Lemma eqb_val_reflect : forall v1 v2, reflect (v1 = v2) (eqb_val v1 v2).
Proof.
  intros; reflect_split; auto; subst.
  rewrite eqb_val_refl in Heqb; discriminate.
Qed.

Global Instance ValueEqDec : EqDec Val.t eq :=
  { equiv_dec := fun v1 v2 => reflect_dec _ _ (eqb_val_reflect v1 v2) }.
