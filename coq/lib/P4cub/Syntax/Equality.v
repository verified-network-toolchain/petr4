From Coq Require Import PArith.BinPos
     ZArith.BinInt NArith.BinNat Bool.Bool.
From Poulet4 Require Import P4cub.Syntax.AST
     P4cub.Syntax.IndPrincip P4cub.Syntax.CubNotations.
Import String.

Reserved Infix "=?" (at level 70).

Fixpoint eqb_typ (τ1 τ2 : Typ.t) {struct τ1} : bool :=
  let fix eqbl (ts1 ts2 : list Typ.t) {struct ts1} : bool :=
    match ts1, ts2 with
    | [], []           => true
    | t1::ts1', t2::ts2' => ((t1 =? t2)%typ && eqbl ts1' ts2')%bool
    | _, _             => false
    end in
  match τ1, τ2 with
  | Typ.Bool, Typ.Bool
  | Typ.Error, Typ.Error                 => true
  | Typ.Var X1, Typ.Var X2               => Nat.eqb X1 X2
  | Typ.Bit w1, Typ.Bit w2               => (w1 =? w2)%N
  | Typ.VarBit w1, Typ.VarBit w2         => (w1 =? w2)%N
  | Typ.Int w1, Typ.Int w2               => (w1 =? w2)%positive
  | Typ.Array n1 t1, Typ.Array n2 t2     => (n1 =? n2)%N && (t1 =? t2)%typ
  | Typ.Struct b1 ts1, Typ.Struct b2 ts2 => (Bool.eqb b1 b2) && eqbl ts1 ts2
  | _, _ => false
  end
where "x '=?' y" := (eqb_typ x y) : typ_scope.

Definition lists_eqb (l1 l2 : Lst.t) : bool :=
  match l1, l2 with
  | Lst.Struct, Lst.Struct => true
  | Lst.Array τ₁, Lst.Array τ₂ => (τ₁ =? τ₂)%typ
  | Lst.Header b₁, Lst.Header b₂ => Bool.eqb b₁ b₂
  | _, _ => false
  end.

Section TypeEquivalence.
  Local Hint Rewrite PeanoNat.Nat.eqb_refl : core.
  Local Hint Rewrite Pos.eqb_refl : core.
  Local Hint Rewrite @eqb_list_refl : core.
  Local Hint Rewrite @equiv_dec_refl : core.
  Local Hint Rewrite N.eqb_refl.
  Hint Extern 4 => equiv_dec_refl_tactic : core.
  Local Hint Rewrite eqb_reflx : core.
  
  Lemma eqb_typ_refl : forall τ, (τ =? τ)%typ = true.
  Proof.
    induction τ using custom_typ_ind; unravel;
      autorewrite with core; auto;
      try ind_list_Forall;
      intuition; autorewrite with core;
      repeat (rewrite_true; unravel); auto.
  Qed.
    
  Ltac eauto_too_dumb :=
    match goal with
    | H: ?f ?x ?y = ?z,
        IH: (forall y, ?f ?x y = ?z -> _)
      |- _ => apply IH in H; clear IH
    end.

  Local Hint Resolve eqb_prop : core.
  Local Hint Resolve PeanoNat.Nat.eqb_eq : core.
  Local Hint Resolve Peqb_true_eq : core.
    
  Ltac helper :=
    match goal with
    | H: Nat.eqb _ _ = true
      |- _ => apply PeanoNat.Nat.eqb_eq in H; subst; auto
    | H: String.eqb _ _ = true
      |- _ => rewrite String.eqb_eq in H; subst; auto
    | H: (_ =? _)%positive = true
      |- _ => apply Peqb_true_eq in H; subst; auto
    | H: eqb_list _ _ = true
      |- _ => apply eqb_list_eq in H
    end.

  Hint Extern 5 => helper : core.
    
  Lemma eqb_typ_eq : forall t1 t2, (t1 =? t2)%typ = true -> t1 = t2.
  Proof.
    induction t1 using custom_typ_ind; intros []; intros; unravel in *;
      try discriminate; repeat destruct_andb; auto; f_equal;
      repeat destruct_lifted_andb; unravel in *; subst; auto;
      try match goal with
          | IH: Forall _ ?ts1,
              H: _ ?ts1 ?ts2 = true
            |- _ => generalize dependent ts2;
                  induction ts1; intros []; intros;
                  try discriminate; try inv_Forall_cons;
                  repeat destruct_andb; intuition;
                  repeat eauto_too_dumb; subst; auto
          end;
      auto using InitialRing.Neqb_ok.
  Qed.

  Local Hint Resolve eqb_typ_refl : core.
  Local Hint Resolve eqb_typ_eq : core.
  
  Lemma eqb_typ_eq_iff : forall t1 t2 : Typ.t,
      (t1 =? t2)%typ = true <-> t1 = t2.
  Proof.
    intros t1 t2; split; intros; subst; auto.
  Qed.

  Local Hint Resolve eqb_typ_eq_iff : core.
  
  Lemma eqb_typ_reflect : forall t1 t2, reflect (t1 = t2) (t1 =? t2)%typ.
  Proof.
    intros; reflect_split; auto.
    apply eqb_typ_eq_iff in H;
      rewrite H in Heqb; discriminate.
  Defined.
    
  Transparent eqb_typ_reflect.

  Lemma eq_dec : forall t1 t2 : Typ.t,
      t1 = t2 \/ t1 <> t2.
  Proof.
    intros t1 t2. pose proof eqb_typ_reflect t1 t2 as H.
    inv H; auto.
  Qed.

  Lemma lists_eqb_refl : forall l, lists_eqb l l = true.
  Proof.
    intros []; simpl; autorewrite with core; auto.
  Qed.

  Lemma lists_eqb_eq : forall l₁ l₂, lists_eqb l₁ l₂ = true -> l₁ = l₂.
  Proof.
    intros [] [] h; simpl in *; try discriminate;
      f_equal; auto.
  Qed.

  Local Hint Resolve lists_eqb_refl : core.
  Local Hint Resolve lists_eqb_eq : core.
  
  Lemma lists_eqb_eq_iff : forall l₁ l₂,
      lists_eqb l₁ l₂ = true <-> l₁ = l₂.
  Proof.
    firstorder (subst; auto).
  Qed.

  Lemma lists_eqb_reflect : forall l₁ l₂,
      reflect (l₁ = l₂) (lists_eqb l₁ l₂).
  Proof.
    intros; reflect_split; auto.
    apply lists_eqb_eq_iff in H;
      rewrite H in Heqb; discriminate.
  Defined.
End TypeEquivalence.
  
Global Instance TypeEqDec : EqDec Typ.t eq :=
  { equiv_dec := fun t1 t2 => reflect_dec _ _ (eqb_typ_reflect t1 t2) }.

Global Instance ListsEqDec : EqDec Lst.t eq :=
  { equiv_dec := fun l₁ l₂ => reflect_dec _ _ (lists_eqb_reflect l₁ l₂) }.

(** Decidable Expression Equivalence. *)
Global Instance UopEqDec : EqDec Una.t eq.
Proof.
  intros [] []; unravel in *; firstorder;
    try (right; intros ?; discriminate).
Defined.
  
Global Instance BopEqDec : EqDec Bin.t eq.
Proof.
  intros [] []; unfold equiv, complement in *;
    auto 2; right; intros ?; discriminate.
Defined.
    
(** Decidable Expression Equivalence. *)
Fixpoint eqb_exp (e1 e2 : Exp.t) {struct e1} : bool :=
  let fix lstruct (es1 es2 : list Exp.t) : bool :=
    match es1, es2 with
    | [], _::_ | _::_, [] => false
    | [], [] => true
    | e1::es1, e2::es2 => (e1 =? e2)%exp && lstruct es1 es2
    end in
  match e1, e2 with
  | Exp.Bool b1, Exp.Bool b2 => Bool.eqb b1 b2
  | (w1 `W n1)%exp, (w2 `W n2)%exp
    => (w1 =? w2)%N && (n1 =? n2)%Z
  | (w1 `S z1)%exp, (w2 `S z2)%exp
    => (w1 =? w2)%positive && (z1 =? z2)%Z
  | Exp.VarBit m1 w1 n1, Exp.VarBit m2 w2 n2
    => (m1 =? m2)%N && (w1 =? w2)%N && (n1 =? n2)%Z
  | Exp.Var τ1 og1 x1, Exp.Var τ2 og2 x2
    => PeanoNat.Nat.eqb x1 x2 && (og1 =? og2)%string && (τ1 =? τ2)%typ
  | Exp.Slice h1 l1 e1, Exp.Slice h2 l2 e2
    => (h1 =? h2)%positive && (l1 =? l2)%positive && (e1 =? e2)%exp
  | Exp.Cast τ1 e1, Exp.Cast τ2 e2
    => (τ1 =? τ2)%typ && (e1 =? e2)%exp
  | Exp.Uop t2 u1 e1, Exp.Uop t1 u2 e2
    => equiv_dec u1 u2 &&&& (e1 =? e2)%exp && (t1 =? t2)%typ
  | Exp.Bop t1 o1 el1 er1, Exp.Bop t2 o2 el2 er2
    => equiv_dec o1 o2 &&&& (el1 =? el2)%exp && (er1 =? er2)%exp && (t1 =? t2)%typ
  | Exp.Index t1 a1 b1, Exp.Index t2 a2 b2
    => (t1 =? t2)%typ && (a1 =? a2)%exp && (b1 =? b2)%exp
  | Exp.Member t1 x1 e1, Exp.Member t2 x2 e2
    => PeanoNat.Nat.eqb x1 x2 && (e1 =? e2)%exp && (t1 =? t2)%typ
  | Exp.Lists l1 es1, Exp.Lists l2 es2
    => lists_eqb l1 l2 && lstruct es1 es2
  | Exp.Error err1, Exp.Error err2
    => if equiv_dec err1 err2 then true else false
  | _, _ => false
  end
where "x '=?' y" := (eqb_exp x y) : exp_scope.

Section ExprEquivalenceDefs.
  Local Hint Rewrite String.eqb_refl : core.
  Local Hint Rewrite eqb_reflx : core.
  Local Hint Rewrite Pos.eqb_refl : core.
  Local Hint Rewrite Z.eqb_refl : core.
  Local Hint Rewrite eqb_typ_refl : core.
  Local Hint Rewrite lists_eqb_refl : core.
  Local Hint Extern 5 => equiv_dec_refl_tactic : core.
  Local Hint Rewrite PeanoNat.Nat.eqb_refl : core.
  Local Hint Rewrite @eqb_list_refl : core.
  Local Hint Rewrite @equiv_dec_refl : core.
  Local Hint Rewrite N.eqb_refl : core.
  Local Hint Resolve eqb_reflx : core.

  Lemma eqb_exp_refl : forall exp : Exp.t, (exp =? exp)%exp = true.
  Proof.
    intro exp; induction exp using custom_exp_ind;
      cbn; autorewrite with core;
      try match goal with
        | H: predop _ _ |- _ => inv H
        end;
      try ind_list_Forall; cbn in *;
      repeat match goal with
        | H: ?trm = true |- context [ ?trm ] => rewrite H; clear H
        end; cbn in *; auto.
  Qed.

  Local Hint Resolve eqb_prop : core.
  Local Hint Resolve PeanoNat.Nat.eqb_eq : core.
  Local Hint Resolve EqNat.beq_nat_true : core.
  Local Hint Resolve Peqb_true_eq : core.
  Local Hint Resolve lists_eqb_eq : core.
  
  Ltac eq_true_terms :=
    match goal with
    | H: Bool.eqb _ _ = true |- _
      => apply eqb_prop in H; subst
    | H: (_ =? _)%string = true |- _
      => rewrite String.eqb_eq in H; subst
    | H: (_ =? _)%N = true |- _
      => apply InitialRing.Neqb_ok in H; subst
    | H: (_ =? _)%positive = true |- _
      => apply Peqb_true_eq in H; subst
    | H: (_ =? _)%Z = true |- _
      => apply Z.eqb_eq in H; subst
    | H: _ && _ = true |- _
      => apply andb_true_iff in H as [? ?]
    | H: context [equiv_dec ?x1 ?x2 &&&& _] |- _
      => destruct (equiv_dec x1 x2) as [? | ?];
        unravel in H; try discriminate
    | H: context [if equiv_dec ?t1 ?t2 then _ else _] |- _
      => destruct (equiv_dec t1 t2) as [? | ?];
        unravel in H; try discriminate
    | H: context [if eqb_typ ?t1 ?t2 then _ else _] |- _
      => destruct (eqb_typ t1 t2) eqn:?;
                 unravel in H; try discriminate
    | H: context [eqb_typ ?t1 ?t2 && _] |- _
      => destruct (eqb_typ t1 t2) eqn:?;
                 unravel in H; try discriminate
    | H: context [eqb_exp ?e1 ?e2 && _] |- _
      => destruct (eqb_exp e1 e2) eqn:?;
                 unravel in H; try discriminate
    | H: eqb_typ _ _ = true |- _
      => apply eqb_typ_eq_iff in H
    | H: context [if eqb_exp ?e1 ?e2 then _ else _] |- _
      => destruct (eqb_exp e1 e2) eqn:?;
                 unravel in H; try discriminate
    | H: eqb_exp ?e1 _ = true,
        IH: forall e2, eqb_exp ?e1 e2 = true -> ?e1 = e2 |- _
      => apply IH in H
    | H: _ === _ |- _ => unfold equiv in H;
                       match goal with
                       | H: _ = _ |- _ => subst
                       end
    | H: equiv _ _ |- _ => unfold equiv in H;
                         match goal with
                         | H: _ = _ |- _ => subst
                         end
    | H: Forall _ (_ :: _) |- _ => inv H
    | H: ?P, IH: ?P -> ?Q |- _ => apply IH in H as ?
    | H: (if ?trm then true else false) = true |- _
      => destruct trm eqn:?; unravel in H; try discriminate
    end.
    
  Local Hint Extern 5 => eq_true_terms : core.
    
  Lemma eqb_exp_eq : forall e1 e2 : Exp.t,
      (e1 =? e2)%exp = true -> e1 = e2.
  Proof.
    induction e1 using custom_exp_ind;
      intros [] ?; unravel in *;
      try discriminate; auto 1;
      repeat eq_true_terms;
      unfold equiv in *;
      subst; auto; try constructor; auto 1; f_equal; auto.
    - rename es into l1; rename es0 into l2.
      generalize dependent l2.
      ind_list_Forall; intros [| h2 l2] He; try discriminate; auto.
      apply andb_prop in He as [He1 He2]; f_equal; eauto.
  Qed.
  
  Local Hint Resolve eqb_exp_refl : core.
  Local Hint Resolve eqb_exp_eq : core.
    
  Lemma eqb_exp_iff : forall e1 e2 : Exp.t,
      (e1 =? e2)%exp = true <-> e1 = e2.
  Proof. intros; split; intros; subst; auto. Qed.
    
  Local Hint Resolve eqb_exp_iff : core.
  Local Hint Extern 5 =>
         match goal with
         | H: eqb_exp ?e1 ?e2 = false,
             H': ?e1 = ?e2 |- False
           => apply eqb_exp_iff in H'; rewrite H' in H; discriminate
  end : core.
  
  Lemma eqb_exp_reflect : forall e1 e2 : Exp.t,
      reflect (e1 = e2) (e1 =? e2)%exp.
  Proof.
    intros; reflect_split; auto 2;
      autorewrite with core; auto 2.
  Qed.
End ExprEquivalenceDefs.
  
Global Instance ExprEqDec {tags_t : Type} : EqDec Exp.t eq :=
  { equiv_dec := fun e1 e2 => reflect_dec _ _ (eqb_exp_reflect e1 e2) }.
