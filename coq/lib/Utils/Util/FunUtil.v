Require Export Poulet4.Monads.Option Coq.Classes.EquivDec.
Require Import Basics.

(** * Combinators *)

Definition pipeline {A B : Type} (x : A) (f : A -> B) : B := f x.

Infix "▷" := pipeline (at level 45, left associativity).

Infix "∘" := compose (at level 40, left associativity).

Infix "$" := apply (at level 41, right associativity).

(** * Reduction Tactics *)

Tactic Notation "unravel" :=
  simpl;
  unfold "∘", "$", "▷",
  mret, mbind, option_bind,
  equiv, complement; simpl.

Tactic Notation "unravel" "in" hyp(H) :=
  simpl in H;
  unfold "∘", "$", "▷",
  mret, mbind, option_bind,
  equiv, complement in H; simpl in H.

Tactic Notation "unravel" "in" "*" :=
  simpl in *;
  unfold "∘", "$", "▷",
  mret, mbind, option_bind,
  equiv, complement in *; simpl in *.

Ltac inv H := inversion H; clear H; subst.

Ltac inv_eq :=
        match goal with
        | H: _ = _ |- _ => inv H
        end.

Ltac some_inv :=
  match goal with
  | H: Some _ = Some _ |- _ => inv H
  end.

Tactic Notation "match_some_inv" "as" simple_intropattern(E) :=
  match goal with
  | H: match ?trm with Some _ => _ | None => _ end = Some _
    |- _ => destruct trm as [? |] eqn:E ; cbn in *;
          try discriminate
  end.

Tactic Notation "match_some_inv" := match_some_inv as ?.

Ltac pair_destr :=
  lazymatch goal with
  | h: (_,_) = (_,_) |- _ => inv h
  end.

Ltac conj_destr :=
  lazymatch goal with
    h: _ /\ _ |- _ => destruct h as [? ?]
  end.

Ltac let_destr_pair :=
  lazymatch goal with
  | h: context [let (_,_) := ?a in _] |- _
    => rewrite surjective_pairing with (p:=a) in h; cbn
  | |- context [let (_,_) := ?a in _]
    => rewrite surjective_pairing with (p:=a); cbn
  end.

Ltac pair_fst_snd_eqns :=
  lazymatch goal with
    h: _ = (_,_) |- _
    => pose proof f_equal fst h as ?; pose proof f_equal snd h as ?; clear h;
      cbn in *; subst; cbn in *
  end.

(** * Utility Definitions *)

Section MapProd.
  Polymorphic Universes a b c.
  Polymorphic Context {A : Type@{a}} {B : Type@{b}} {C : Type@{c}}.
  Polymorphic Variable f : A -> B.

  Polymorphic Definition prod_map_fst '((a,c) : A * C) : B * C := (f a, c).

  Polymorphic Definition prod_map_snd '((c,a) : C * A) : C * B := (c, f a).

  Polymorphic Lemma fst_prod_map_fst : forall ac,
      fst (prod_map_fst ac) = f (fst ac).
  Proof using. intros [? ?]; reflexivity. Qed.

  Polymorphic Lemma snd_prod_map_fst : forall ac,
      snd (prod_map_fst ac) = snd ac.
  Proof using. intros [? ?]; reflexivity. Qed.
  
  Polymorphic Lemma snd_prod_map_snd : forall ca,
      snd (prod_map_snd ca) = f (snd ca).
  Proof using. intros [? ?]; reflexivity. Qed.

  Polymorphic Lemma fst_prod_map_snd : forall ca,
      fst (prod_map_snd ca) = fst ca.
  Proof using. intros [? ?]; reflexivity. Qed.
End MapProd.

Fixpoint n_compose {A : Type} (n : nat) (f : A -> A) (x : A) : A :=
  match n with
  | O => x
  | S n => n_compose n f (f x)
  end.

Section Curry3.
  Context {A B C D : Type}.

  Definition curry3 
             (f : A * B * C -> D) : A -> B -> C -> D :=
    fun a b c => f (a,b,c).
  
  Definition uncurry3
             (f : A -> B -> C -> D) : A * B * C -> D :=
    fun '(a,b,c) => f a b c.
End Curry3.

Section Curry4.
  Context {A B C D E : Type}.

  Definition curry4  (f : A * B * C * D -> E) : A -> B -> C -> D -> E :=
    fun a b c d => f (a,b,c,d).

  Definition uncurry4 (f : A -> B -> C -> D -> E) : A * B * C * D -> E :=
    fun '(a,b,c,d) => f a b c d.
End Curry4.

Section Triple.
  Context {A B C : Type}.
  
  Definition triple_1 '((a,_,_) : A * B * C) : A := a.

  Definition triple_2 '((_,b,_) : A * B * C) : B := b.

  Definition triple_3 '((_,_,c) : A * B * C) : C := c.
End Triple.

Section Fourple.
  Context {A B C D : Type}.

  Definition fourple_1 '((a,_,_,_) : A * B * C * D) : A := a.

  Definition fourple_2 '((_,b,_,_) : A * B * C * D) : B := b.

  Definition fourple_3 '((_,_,c,_) : A * B * C * D) : C := c.
  
  Definition fourple_4 '((_,_,_,d) : A * B * C * D) : D := d.
End Fourple.

Definition
  map_sum
  {A B C D : Type} (f : A -> B) (g : C -> D) (e : A + C) : B + D :=
  match e with
  | inl a => inl (f a)
  | inr b => inr (g b)
  end.

Section OExists.
  Context {A : Set}.
  Variable P : A -> Prop.

  Variant OExists : option A -> Prop :=
    OExist_some a :
      P a -> OExists (Some a).

  Local Hint Constructors OExists : core.

  Lemma OExists_exists : forall o : option A,
      OExists o <-> exists a, P a /\ o = Some a.
  Proof using.
    intros [a |]; split.
    - intro h; inv h; eauto.
    - intros (a' & H & h); inv h; auto.
    - intro h; inv h.
    - intros (a' & H & h); inv h.
  Qed.
End OExists.

Section OptionEffect.
  Polymorphic Universes a b c.
  Polymorphic Context {A : Type@{a}} {B : Type@{b}} {C : Type@{a}}.
  Polymorphic Variable default : C.
  Polymorphic Variable f : A -> B * C.
  Polymorphic Variable R : A -> B -> C -> Prop.

  Polymorphic Definition omap_effect (o : option A) : option B * C :=
    match o with
    | Some a => let '(b, c) := f a in (Some b, c)
    | None   => (None, default)
    end.
  
  Polymorphic Variant orelate_effect : option A -> option B -> C -> Prop :=
    | orelate_effect_some a b c :
      R a b c ->
      orelate_effect (Some a) (Some b) c
    | orelate_effect_none :
      orelate_effect None None default.

  Polymorphic Hypothesis f_R : forall a,
      R a (fst (f a)) (snd (f a)).

  Local Hint Constructors orelate_effect : core.
  
  Polymorphic Lemma omap_orelate_effect : forall o,
      orelate_effect o (fst (omap_effect o)) (snd (omap_effect o)).
  Proof using A B C R default f f_R.
    intros [a |]; cbn; auto.
    destruct (f a) as [b c] eqn:fa. cbn.
    pose proof f_equal fst fa as ffst.
    pose proof f_equal snd fa as fsnd.
    cbn in *.
    rewrite <- ffst, <- fsnd.
    auto.
  Qed.

  Polymorphic Hypothesis R_f : forall a b c,
      R a b c -> f a = (b, c).

  Polymorphic Lemma orelate_omap_effect : forall oa ob c,
      orelate_effect oa ob c ->
      omap_effect oa = (ob, c).
  Proof using A B C R R_f default f.
    intros [a |] [b |] c h; inv h; cbn; try reflexivity.
    erewrite R_f with (b:=b) (c:=c) by assumption.
    reflexivity.
  Qed.
End OptionEffect.

Section Forall_Sum.
  Polymorphic Universes a b.
  Polymorphic Context {A : Type@{a}} {B : Type@{b}}.
  Polymorphic Variables (P : A -> Prop) (Q : B -> Prop).

  Polymorphic Variant SumForall : A + B -> Prop :=
    | Forall_inl a : P a -> SumForall (inl a)
    | Forall_inr b : Q b -> SumForall (inr b).
End Forall_Sum.
  

Reserved Infix "`^" (at level 10, left associativity).

Fixpoint mapply {A : Set} (f : A -> A) (m : nat) (a : A) : A :=
  match m with
  | O => a
  | S m => f $ f `^ m a
  end
where "f `^ m" := (mapply f m).

Section mapply.
  Context {A : Set}.
  Variable f : A -> A.

  Lemma mapply0 : forall a, f `^ 0 a = a.
  Proof using.
    reflexivity.
  Qed.

  Lemma mapply1 : forall a, f `^ 1 a = f a.
  Proof using.
    reflexivity.
  Qed.
End mapply.

Lemma forall_conj_distr (U : Type) (P Q : U -> Prop) :
    (forall u, P u /\ Q u) <-> (forall u, P u) /\ forall u, Q u.
Proof.
  firstorder.
Qed.
