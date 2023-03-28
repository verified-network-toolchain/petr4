Require Coq.Vectors.Vector.
Module Vec := Coq.Vectors.Vector.
From Equations Require Import Equations.
Require Import Poulet4.Utils.Util.FunUtil.

Module VecEquations.
  Derive Signature NoConfusion NoConfusionHom for Vec.t.
End VecEquations.

Definition vec_sum {n : nat} (v : Vec.t nat n) : nat :=
  Vec.fold_right Nat.add v 0.

Section Lemmas.
  Import Vec.VectorNotations.
  Local Open Scope vector_scope.
  
  Polymorphic Universes a b c.
  Polymorphic Context {A : Type@{a}} {B : Type@{b}} {C : Type@{c}}.
  Polymorphic Variable f : B -> C.

  Polymorphic Lemma vec_map_snd_map : forall {n : nat} (v : Vec.t (A * B) n),
      Vec.map snd (Vec.map (fun '(a, b) => (a, f b)) v) = Vec.map f (Vec.map snd v).
  Proof using.
    intros n v.
    depind v; unravel; trivial.
    destruct h as [a b]; unravel.
    f_equal. assumption.
  Qed.

  Polymorphic Lemma vec_map_fst_map : forall {n : nat} (v : Vec.t (B * A) n),
      Vec.map fst (Vec.map (fun '(b, a) => (f b, a)) v) = Vec.map f (Vec.map fst v).
  Proof using.
    intros n v.
    depind v; unravel; trivial.
    destruct h as [b a].
    f_equal. assumption.
  Qed.

  Polymorphic Lemma vec_ignore_map_fst_map : forall {n : nat} (v : Vec.t (A * B) n),
      Vec.map fst (Vec.map (fun '(a, b) => (a, f b)) v) = Vec.map fst v.
  Proof using.
    intros n v.
    depind v; unravel; trivial.
    destruct h as [a b]. f_equal. assumption.
  Qed.

  Polymorphic Lemma vec_ignore_map_snd_map : forall {n : nat} (v : Vec.t (B * A) n),
      Vec.map snd (Vec.map (fun '(b, a) => (f b, a)) v) = Vec.map snd v.
  Proof using.
    intros n v.
    depind v; unravel; trivial.
    destruct h as [b a]. f_equal. assumption.
  Qed.
End Lemmas.
