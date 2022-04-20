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

(** * Utility Functions *)

Fixpoint n_compose { A : Type } (n : nat) (f : A -> A) (x : A) : A :=
  match n with
  | O => x
  | S n => n_compose n f (f x)
  end.

Definition curry3 {A B C D : Type}
           (f : A * B * C -> D) : A -> B -> C -> D :=
  fun a b c => f (a,b,c).
(**[]*)

Definition uncurry3 {A B C D : Type}
           (f : A -> B -> C -> D) '((a,b,c) : A * B * C) : D :=
  f a b c.
(**[]*)

Definition curry4 {A B C D E : Type}
           (f : A * B * C * D -> E) : A -> B -> C -> D -> E :=
  fun a b c d => f (a,b,c,d).
(**[]*)

Definition uncurry4 {A B C D E : Type}
           (f : A -> B -> C -> D -> E) '((a,b,c,d) : A * B * C * D) : E :=
  f a b c d.
(**[]*)

Definition triple_1 {A B C : Type}  '((a,_,_) : A * B * C) : A := a.

Definition triple_2 {A B C : Type}  '((_,b,_) : A * B * C) : B := b.

Definition triple_3 {A B C : Type}  '((_,_,c) : A * B * C) : C := c.

Definition fourple_1 {A B C D : Type}  '((a,_,_,_) : A * B * C * D) : A := a.

Definition fourple_2 {A B C D : Type}  '((_,b,_,_) : A * B * C * D) : B := b.

Definition fourple_3 {A B C D : Type}  '((_,_,c,_) : A * B * C * D) : C := c.

Definition fourple_4 {A B C D : Type}  '((_,_,_,d) : A * B * C * D) : D := d.

Definition
  map_sum
  {A B C D : Type} (f : A -> B) (g : C -> D) (e : A + C) : B + D :=
  match e with
  | inl a => inl (f a)
  | inr b => inr (g b)
  end.
