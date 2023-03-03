From Coq Require Import PArith.BinPos
     ZArith.BinInt NArith.BinNat Bool.Bool.
From Poulet4 Require Import P4cub.Syntax.AST
     P4cub.Syntax.IndPrincip P4cub.Syntax.CubNotations.
Import String Expr ExprNotations.

Reserved Infix "=?" (at level 70).

Fixpoint eqbt (τ1 τ2 : t) {struct τ1} : bool :=
  let fix eqbl (ts1 ts2 : list t) {struct ts1} : bool :=
    match ts1, ts2 with
    | [], []           => true
    | t1::ts1', t2::ts2' => ((t1 =? t2)%ty && eqbl ts1' ts2')%bool
    | _, _             => false
    end in
  match τ1, τ2 with
  | TBool, TBool
  | TError, TError                 => true
  | TVar X1, TVar X2               => Nat.eqb X1 X2
  | TBit w1, TBit w2               => (w1 =? w2)%N
  | TVarBit w1, TVarBit w2         => (w1 =? w2)%N
  | TInt w1, TInt w2               => (w1 =? w2)%positive
  | TArray n1 t1, TArray n2 t2     => (n1 =? n2)%N && (t1 =? t2)%ty
  | TStruct b1 ts1, TStruct b2 ts2 => (Bool.eqb b1 b2) && eqbl ts1 ts2
  | _, _ => false
  end
where "x '=?' y" := (eqbt x y) : ty_scope.

Definition lists_eqb (l1 l2 : Expr.lists) : bool :=
  match l1, l2 with
  | lists_struct, lists_struct => true
  | lists_array τ₁, lists_array τ₂ => (τ₁ =? τ₂)%ty
  | lists_header b₁, lists_header b₂ => Bool.eqb b₁ b₂
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
  
  Lemma eqbt_refl : forall τ, (τ =? τ)%ty = true.
  Proof.
    induction τ using custom_t_ind; unravel;
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
    
  Lemma eqbt_eq : forall t1 t2, (t1 =? t2)%ty = true -> t1 = t2.
  Proof.
    induction t1 using custom_t_ind; intros []; intros; unravel in *;
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

  Local Hint Resolve eqbt_refl : core.
  Local Hint Resolve eqbt_eq : core.
  
  Lemma eqbt_eq_iff : forall t1 t2 : t,
      (t1 =? t2)%ty = true <-> t1 = t2.
  Proof.
    intros t1 t2; split; intros; subst; auto.
  Qed.

  Local Hint Resolve eqbt_eq_iff : core.
  
  Lemma eqbt_reflect : forall t1 t2, reflect (t1 = t2) (t1 =? t2)%ty.
  Proof.
    intros; reflect_split; auto.
    apply eqbt_eq_iff in H;
      rewrite H in Heqb; discriminate.
  Defined.
    
  Transparent eqbt_reflect.

  Lemma eq_dec : forall t1 t2 : t,
      t1 = t2 \/ t1 <> t2.
  Proof.
    intros t1 t2. pose proof eqbt_reflect t1 t2 as H.
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
  
Global Instance TypeEqDec : EqDec t eq :=
  { equiv_dec := fun t1 t2 => reflect_dec _ _ (eqbt_reflect t1 t2) }.

Global Instance ListsEqDec : EqDec lists eq :=
  { equiv_dec := fun l₁ l₂ => reflect_dec _ _ (lists_eqb_reflect l₁ l₂) }.

(** Decidable Expression Equivalence. *)
Global Instance UopEqDec : EqDec uop eq.
Proof.
  intros [] []; unravel in *; firstorder;
    try (right; intros ?; discriminate).
  elim validity; elim validity0; auto;
    try (right; intros ?; discriminate).
Defined.
  
Global Instance BopEqDec : EqDec bop eq.
Proof.
  intros [] []; unfold equiv, complement in *;
    auto 2; right; intros ?; discriminate.
Defined.
    
(** Decidable Expression Equivalence. *)
Fixpoint eqbe (e1 e2 : e) {struct e1} : bool :=
  let fix lstruct (es1 es2 : list e) : bool :=
    match es1, es2 with
    | [], _::_ | _::_, [] => false
    | [], [] => true
    | e1::es1, e2::es2 => (e1 =? e2)%expr && lstruct es1 es2
    end in
  match e1, e2 with
  | Bool b1, Bool b2 => Bool.eqb b1 b2
  | w1 `W n1, w2 `W n2
    => (w1 =? w2)%N && (n1 =? n2)%Z
  | w1 `S z1, w2 `S z2
    => (w1 =? w2)%positive && (z1 =? z2)%Z
  | VarBit m1 w1 n1, VarBit m2 w2 n2
    => (m1 =? m2)%N && (w1 =? w2)%N && (n1 =? n2)%Z
  | Var τ1 og1 x1, Var τ2 og2 x2
    => PeanoNat.Nat.eqb x1 x2 && (og1 =? og2)%string && (τ1 =? τ2)%ty
  | Slice h1 l1 e1, Slice h2 l2 e2
    => (h1 =? h2)%positive && (l1 =? l2)%positive && (e1 =? e2)%expr
  | Cast τ1 e1, Cast τ2 e2
    => (τ1 =? τ2)%ty && (e1 =? e2)%expr
  | Uop t2 u1 e1, Uop t1 u2 e2
    => equiv_dec u1 u2 &&&& (e1 =? e2)%expr && (t1 =? t2)%ty
  | Bop t1 o1 el1 er1, Bop t2 o2 el2 er2
    => equiv_dec o1 o2 &&&& (el1 =? el2)%expr && (er1 =? er2)%expr && (t1 =? t2)%ty
  | Index t1 a1 b1, Index t2 a2 b2
    => (t1 =? t2)%ty && (a1 =? a2)%expr && (b1 =? b2)%expr
  | Member t1 x1 e1, Member t2 x2 e2
    => PeanoNat.Nat.eqb x1 x2 && (e1 =? e2)%expr && (t1 =? t2)%ty
  | Lists l1 es1, Lists l2 es2
    => lists_eqb l1 l2 && lstruct es1 es2
  | Error err1, Error err2
    => if equiv_dec err1 err2 then true else false
  | _, _ => false
  end
where "x '=?' y" := (eqbe x y) : expr_scope.

Section ExprEquivalenceDefs.
  Local Hint Rewrite String.eqb_refl : core.
  Local Hint Rewrite eqb_reflx : core.
  Local Hint Rewrite Pos.eqb_refl : core.
  Local Hint Rewrite Z.eqb_refl : core.
  Local Hint Rewrite eqbt_refl : core.
  Local Hint Rewrite lists_eqb_refl : core.
  Local Hint Extern 5 => equiv_dec_refl_tactic : core.
  Local Hint Rewrite PeanoNat.Nat.eqb_refl : core.
  Local Hint Rewrite @eqb_list_refl : core.
  Local Hint Rewrite @equiv_dec_refl : core.
  Local Hint Rewrite N.eqb_refl : core.
  Local Hint Resolve eqb_reflx : core.

  Lemma eqbe_refl : forall exp : e, (exp =? exp)%expr = true.
  Proof.
    intro exp; induction exp using custom_e_ind;
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
    | H: context [if eqbt ?t1 ?t2 then _ else _] |- _
      => destruct (eqbt t1 t2) eqn:?;
                 unravel in H; try discriminate
    | H: context [eqbt ?t1 ?t2 && _] |- _
      => destruct (eqbt t1 t2) eqn:?;
                 unravel in H; try discriminate
    | H: context [eqbe ?e1 ?e2 && _] |- _
      => destruct (eqbe e1 e2) eqn:?;
                 unravel in H; try discriminate
    | H: eqbt _ _ = true |- _
      => apply eqbt_eq_iff in H
    | H: context [if eqbe ?e1 ?e2 then _ else _] |- _
      => destruct (eqbe e1 e2) eqn:?;
                 unravel in H; try discriminate
    | H: eqbe ?e1 _ = true,
        IH: forall e2, eqbe ?e1 e2 = true -> ?e1 = e2 |- _
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
    
  Lemma eqbe_eq : forall e1 e2 : e,
      (e1 =? e2)%expr = true -> e1 = e2.
  Proof.
    induction e1 using custom_e_ind;
      intros [] ?; unravel in *;
      try discriminate; auto 1;
      repeat eq_true_terms;
      unfold equiv in *;
      subst; auto; try constructor; auto 1; f_equal; auto.
    - rename exps into l1; rename es into l2.
      generalize dependent l2.
      ind_list_Forall; intros [| h2 l2] He; try discriminate; auto.
      apply andb_prop in He as [He1 He2]; f_equal; eauto.
  Qed.
  
  Local Hint Resolve eqbe_refl : core.
  Local Hint Resolve eqbe_eq : core.
    
  Lemma eqbe_iff : forall e1 e2 : e,
      (e1 =? e2)%expr = true <-> e1 = e2.
  Proof. intros; split; intros; subst; auto. Qed.
    
  Local Hint Resolve eqbe_iff : core.
  Local Hint Extern 5 =>
         match goal with
         | H: eqbe ?e1 ?e2 = false,
             H': ?e1 = ?e2 |- False
           => apply eqbe_iff in H'; rewrite H' in H; discriminate
  end : core.
  
  Lemma eqbe_reflect : forall e1 e2 : e,
      reflect (e1 = e2) (e1 =? e2)%expr.
  Proof.
    intros; reflect_split; auto 2;
      autorewrite with core; auto 2.
  Qed.
End ExprEquivalenceDefs.
  
Global Instance ExprEqDec {tags_t : Type} : EqDec e eq :=
  { equiv_dec := fun e1 e2 => reflect_dec _ _ (eqbe_reflect e1 e2) }.