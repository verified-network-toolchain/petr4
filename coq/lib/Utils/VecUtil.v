Require Coq.Vectors.Vector.
Module Vec := Coq.Vectors.Vector.
From Equations Require Import Equations.
Require Import Poulet4.Utils.Util.FunUtil.

Derive NoConfusion NoConfusionHom Subterm for nat.

Module VecEquations.
  Derive Signature NoConfusion NoConfusionHom Subterm for Vec.t.

  Derive Signature for Vec.Forall.
End VecEquations.

Definition vec_sum {n : nat} (v : Vec.t nat n) : nat :=
  Vec.fold_right Nat.add v 0.

Section Lemmas.
  Import Vec.VectorNotations.
  Local Open Scope vector_scope.
  
  Polymorphic Universe a.
  Polymorphic Context {A : Type@{a}}.

  Section ForallForall.
    Polymorphic Variable P : A -> Prop.

    Local Hint Constructors Vec.Forall : core.
    
    Polymorphic Lemma list_Forall_vec : forall (l : list A),
        List.Forall P l -> Vec.Forall P (Vec.of_list l).
    Proof using.
      intros l h; induction h; cbn; auto.
    Qed.

    Local Hint Constructors List.Forall : core.

    Polymorphic Lemma vec_Forall_list : forall {n : nat} (v : Vec.t A n),
        Vec.Forall P v -> List.Forall P (Vec.to_list v).
    Proof using.
      intros n v h. depind h; cbn; auto.
    Qed.
  End ForallForall.
  
  Polymorphic Fixpoint vec_rep (n : nat) (a : A) : Vec.t A n :=
    match n with
    | O => []
    | S n => a :: vec_rep n a
    end.
  
  Polymorphic Universes b.
  Polymorphic Context {B : Type@{b}}.

  Section Foralloflistmap.
    Polymorphic Variable f : A -> B.

    Polymorphic Lemma vec_hd_map : forall {n} (v : Vec.t A (S n)),
        Vec.hd (Vec.map f v) = f (Vec.hd v).
    Proof using.
      intros n v. depelim v; reflexivity.
    Qed.

    Polymorphic Lemma vec_tl_map : forall {n} (v : Vec.t A (S n)),
        Vec.tl (Vec.map f v) = Vec.map f (Vec.tl v).
    Proof using.
      intros n v; depelim v; reflexivity.
    Qed.

    Polymorphic Lemma map_to_list : forall {n} (v : Vec.t A n),
        List.map f (Vec.to_list v) = Vec.to_list (Vec.map f v).
    Proof using.
      intros n v. depind v; cbn; f_equal; auto.
    Qed.
    
    Polymorphic Variable P : B -> Prop.

    Local Hint Constructors Vec.Forall : core.
    
    Polymorphic Lemma Forall_of_list_map : forall (l : list A),
        Vec.Forall P (Vec.of_list (List.map f l)) ->
        Vec.Forall P (Vec.map f (Vec.of_list l)).
    Proof using.
      intro l; induction l as [| a l ih]; intro h; cbn in *; depelim h; auto.
    Qed.

    Polymorphic Lemma Forall_map_of_list : forall (l : list A),
        Vec.Forall P (Vec.map f (Vec.of_list l)) ->
        Vec.Forall P (Vec.of_list (List.map f l)).
    Proof using.
      intro l; induction l as [| a l ih]; intro h; cbn in *; depelim h; auto.
    Qed.
  End Foralloflistmap.
  
  (*Polymorphic Lemma map_of_list : forall (f : A -> B) (l : list A),
    Vec.of_list (List.map f l) = Vec.map f (Vec.of_list l).*)
  
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

  Polymorphic Lemma vec_zip_fst : forall {n : nat} (va : Vec.t A n) (vb : Vec.t B n),
      Vec.map fst (vec_zip va vb) = va.
  Proof using.
    intros n va vb.
    funelim (vec_zip va vb); auto.
    rewrite vec_zip_equation_2; cbn; f_equal; auto.
  Qed.

  Polymorphic Lemma vec_zip_snd : forall {n : nat} (va : Vec.t A n) (vb : Vec.t B n),
      Vec.map snd (vec_zip va vb) = vb.
  Proof using.
    intros n va vb.
    funelim (vec_zip va vb); auto.
    rewrite vec_zip_equation_2; cbn; f_equal; auto.
  Qed.
  
  Polymorphic Equations vec_unzip : forall {n : nat},
      Vec.t (A * B) n -> Vec.t A n * Vec.t B n := {
      vec_unzip [] := ([], []);
      vec_unzip ((a, b) :: v) :=
        let '(va, vb) := vec_unzip v in (a :: va, b :: vb)
    }.

  Polymorphic Lemma vec_unzip_correct : forall {n : nat} (v : Vec.t (A * B) n),
      vec_unzip v = (Vec.map fst v, Vec.map snd v).
  Proof using.
    intros n v.
    funelim (vec_unzip v); cbn; auto.
    rewrite vec_unzip_equation_2, H.
    reflexivity.
  Qed.
  
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

Section Map3.
  Import Vec.VectorNotations.
  Local Open Scope vector_scope.
  
  Polymorphic Universes a b c d.
  Polymorphic Context {A : Type@{a}} {B : Type@{b}} {C : Type@{c}} {D : Type@{d}}.
  Polymorphic Variable f : A -> B -> C -> D.

  Set Equations Transparent.
  
  Polymorphic Equations vec_map3 :
    forall {n : nat}, Vec.t A n -> Vec.t B n -> Vec.t C n -> Vec.t D n := {
      vec_map3 [] [] [] := [];
      vec_map3 (a :: v1) (b :: v2) (c :: v3) :=
        f a b c :: vec_map3 v1 v2 v3
    }.
End Map3.

Section MapRep.
  Polymorphic Universes a b.
  Polymorphic Context {A : Type@{a}} {B : Type@{b}}.
  Polymorphic Variable f : A -> B.
  Polymorphic Variable a : A.

  Polymorphic Lemma vec_rep_map : forall n,
      Vec.map f (vec_rep n a) = vec_rep n (f a).
  Proof using.
    intro n; induction n as [| n ih]; cbn; f_equal; assumption.
  Qed.
End MapRep.
