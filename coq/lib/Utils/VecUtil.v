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
  
  Polymorphic Universe a.
  Polymorphic Context {A : Type@{a}}.

  Polymorphic Fixpoint vec_rep (n : nat) (a : A) : Vec.t A n :=
    match n with
    | O => []
    | S n => a :: vec_rep n a
    end.
  
  Polymorphic Universes b.
  Polymorphic Context {B : Type@{b}}.

  Polymorphic Lemma vec_map2_same : forall {n : nat} (f : A -> A -> B) (v : Vec.t A n),
      Vec.map2 f v v = Vec.map (fun a => f a a) v.
  Proof using.
    intros n f v.
    depind v; unravel; f_equal; auto.
  Qed.

  Polymorphic Equations vec_zip : forall {n : nat},
      Vec.t A n -> Vec.t B n -> Vec.t (A * B) n := {
      vec_zip [] [] := [];
      vec_zip (a :: va) (b :: vb) := (a, b) :: vec_zip va vb
    }.

  Polymorphic Equations vec_unzip : forall {n : nat},
      Vec.t (A * B) n -> Vec.t A n * Vec.t B n := {
      vec_unzip [] := ([], []);
      vec_unzip ((a, b) :: v) :=
        let '(va, vb) := vec_unzip v in (a :: va, b :: vb)
    }.

  Polymorphic Universes c.
  Polymorphic Context {C : Type@{c}}.
  
  Polymorphic Lemma vec_map_rep_r : forall (g : B -> A -> C) {n : nat} (v : Vec.t B n) (a : A),
      Vec.map2 g v (vec_rep n a) = Vec.map (fun b => g b a) v.
  Proof using.
    intros g n v a.
    depind v; unravel; trivial.
    f_equal. auto.
  Qed.

  Polymorphic Lemma vec_map_rep_l : forall (g : A -> B -> C) {n : nat} (v : Vec.t B n) (a : A),
      Vec.map2 g (vec_rep n a) v = Vec.map (g a) v.
  Proof using.
    intros g n v a.
    depind v; unravel; trivial.
    f_equal. auto.
  Qed.
  
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
