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

Ltac match_some_inv :=
  match goal with
  | H: match ?trm with Some _ => _ | None => _ end = Some _
    |- _ => destruct trm as [? |] eqn:? ; cbn in *;
          try discriminate
  end.

(** * Utility Functions *)

Section MapProd.
  Context {A B C : Type}.
  Variable f : A -> B.

  Definition map_fst '((a,c) : A * C) : B * C := (f a, c).

  Definition map_snd '((c,a) : C * A) : C * B := (c, f a).
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
  Proof.
    intros [a |]; split.
    - intro h; inv h; eauto.
    - intros (a' & H & h); inv h; auto.
    - intro h; inv h.
    - intros (a' & H & h); inv h.
  Qed.
End OExists.

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
  Proof.
    reflexivity.
  Qed.

  Lemma mapply1 : forall a, f `^ 1 a = f a.
  Proof.
    reflexivity.
  Qed.
End mapply.

Lemma forall_conj_distr (U : Type) (P Q : U -> Prop) :
    (forall u, P u /\ Q u) <-> (forall u, P u) /\ forall u, Q u.
Proof.
  firstorder.
Qed.
