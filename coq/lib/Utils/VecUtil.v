Require Coq.Vectors.Vector.
Module Vec := Coq.Vectors.Vector.
From Equations Require Import Equations.
Require Import Poulet4.Utils.Util.FunUtil Poulet4.Utils.ForallMap.

Derive NoConfusion NoConfusionHom Subterm for nat.
Derive NoConfusion NoConfusionHom Subterm for list.

Module FinEquations.
  Derive Signature NoConfusion NoConfusionHom Subterm for Fin.t.
End FinEquations.

Module VecEquations.
  Derive Signature NoConfusion NoConfusionHom Subterm for Vec.t.

  Derive Signature for Vec.Forall.

  Derive Signature for Vec.Forall2.
End VecEquations.

Definition vec_sum {n : nat} (v : Vec.t nat n) : nat :=
  Vec.fold_right Nat.add v 0.

Lemma vec_sum_eq_rect : forall {m n : nat} (hmn : m = n) (v : Vec.t nat m),
    vec_sum (eq_rect _ _ v _ hmn) = vec_sum v.
Proof using.
  intros m n hmn v. depelim hmn. reflexivity.
Qed.

Section Lemmas.
  Import List.ListNotations.
  Import Vec.VectorNotations.
  Local Open Scope vector_scope.
  
  Polymorphic Universe a.
  Polymorphic Context {A : Type@{a}}.

  Polymorphic Inductive vec_In (a : A) : forall {n}, Vec.t A n -> Prop :=
  | vec_In_hd {n} (v : Vec.t A n) :
    vec_In a (a :: v)
  | vec_In_tl {n} (h : A) (v : Vec.t A n) :
    vec_In a v -> vec_In a (h :: v).

  Polymorphic Derive Signature for vec_In.
  
  Polymorphic Lemma vec_In_nth : forall a {n} (v : Vec.t A n),
      vec_In a v -> exists m, v [@ m ] = a.
  Proof using.
    intros a n v h. depind h.
    - exists Fin.F1. reflexivity.
    - destruct IHh as [m ih].
      exists (Fin.FS m). cbn. assumption.
  Qed.

  Local Hint Constructors vec_In : core.
  
  Polymorphic Lemma nth_vec_In : forall {n} (m : Fin.t n) (v : Vec.t A n),
      vec_In (v [@ m ]) v.
  Proof using.
    intros n m v.
    depind m; depelim v; cbn; auto.
  Qed.
  
  Section ForallForall.
    Polymorphic Variable P : A -> Prop.

    Local Hint Constructors Vec.Forall : core.
    Local Hint Constructors List.Forall : core.
    
    Polymorphic Lemma vec_Forall_of_list : forall (l : list A),
        Vec.Forall P (Vec.of_list l) <-> List.Forall P l.
    Proof using.
      intro l; split; intro h.
      - induction l; cbn in *; depelim h; auto.
      - induction h; cbn; auto.
    Qed.

    Polymorphic Lemma vec_Forall_forall
      : forall {n} (v : Vec.t A n),
        Vec.Forall P v <-> forall a, vec_In a v -> P a.
    Proof using.
      intros n v; split; intro h.
      - intros a ha. depind h; depelim ha; auto.
      - depind v; auto.
    Qed.
  End ForallForall.
  
  Polymorphic Fixpoint vec_rep (n : nat) (a : A) : Vec.t A n :=
    match n with
    | O => []
    | S n => a :: vec_rep n a
    end.

  Polymorphic Definition vec_concat_list {n : nat} (v : Vec.t (list A) n) : list A :=
    Vec.fold_right (List.app (A:=A)) v []%list.

  Polymorphic Lemma vec_concat_list_nil :
    vec_concat_list [] = []%list.
  Proof using. reflexivity. Qed.

  Polymorphic Lemma vec_concat_list_cons : forall {n : nat} l (v : Vec.t (list A) n),
      vec_concat_list (l :: v) = (l ++ vec_concat_list v)%list.
  Proof using. reflexivity. Qed.

  Polymorphic Lemma length_vec_concat_list : forall {n : nat} (v : Vec.t (list A) n),
      List.length (vec_concat_list v)
      = Vec.fold_right Nat.add (Vec.map (length (A:=A)) v) 0.
  Proof using.
    intros n v; depind v;
      try rewrite vec_concat_list_nil;
      try rewrite vec_concat_list_cons; cbn; trivial.
    rewrite List.app_length.
    f_equal; assumption.
  Qed.

  Polymorphic Lemma list_concat_fold_right : forall (l : list (list A)),
      List.concat l = List.fold_right (List.app (A:=A)) []%list l.
  Proof using.
    intro l; induction l as [| h t ih]; cbn; f_equal; auto.
  Qed.

  Polymorphic Lemma concat_vec_to_list : forall {n} (v : Vec.t (list A) n),
      List.concat (Vec.to_list v) = vec_concat_list v.
  Proof using.
    intros a v.
    rewrite list_concat_fold_right,
      <- Vec.to_list_fold_right.
    reflexivity.
  Qed.

  Polymorphic Lemma vec_to_list_fold_right : forall {n} (v : Vec.t A n),
      Vec.to_list v = Vec.fold_right List.cons v []%list.
  Proof using.
    intros n v. reflexivity.
  Qed.
  
  Polymorphic Universes b.
  Polymorphic Context {B : Type@{b}}.

  Section Forall2.
    Polymorphic Variable R : A -> B -> Prop.
    Local Hint Constructors Vec.Forall2 : core.
  
    Polymorphic Lemma vec_Forall2_forall :
      forall {n} (va : Vec.t A n) (vb : Vec.t B n),
        Vec.Forall2 R va vb <-> forall m, R (va [@ m]) (vb [@ m]).
    Proof using.
      intros n va vb; split; intro h.
      - intro m. depind h.
        + depelim m.
        + depelim m0; cbn; auto.
      - generalize dependent vb.
        depind va; intros vb H; depelim vb; auto.
        pose proof H Fin.F1 as H1; cbn in H1.
        constructor; auto. apply IHva.
        intro m. specialize H with (Fin.FS m).
        cbn in H. assumption.
    Qed.

    Local Hint Constructors List.Forall2 : core.

    Local Hint Resolve PeanoNat.Nat.eq_dec : core.
    Local Hint Resolve Peano_dec.UIP_nat : core.
    
    Polymorphic Lemma vec_Forall2_of_list : forall la lb (hlen : length lb = length la),
        Vec.Forall2 R (Vec.of_list la) (eq_rect _ _ (Vec.of_list lb) _ hlen)
        <-> List.Forall2 R la lb.
    Proof using.
      intro la; induction la as [| a la ih];
        intros [| b lb] hlen; cbn in *;
        try discriminate; split; intro h; auto.
      - rewrite <- Eqdep_dec.eq_rect_eq_dec by auto; auto.
      - assert (hlen' : length lb = length la) by lia.
        replace hlen with (f_equal S hlen') in h by auto.
        rewrite map_subst_map in h. depelim h.
        rewrite ih in h. auto.
      - assert (hlen' : length lb = length la) by lia.
        replace hlen with (f_equal S hlen') by auto.
        rewrite map_subst_map.
        inv h. constructor; auto.
        rewrite ih. assumption.
    Qed.

    Polymorphic Lemma vec_Forall2_eq_rect_l :
      forall {n m} (nm : n = m) (va : Vec.t A n) (vb : Vec.t B m),
        Vec.Forall2 R (eq_rect _ _ va _ nm) vb
        <-> Vec.Forall2 R va (eq_rect _ _ vb _ (eq_sym nm)).
    Proof using.
      intros n m nm va vb. depelim nm.
      reflexivity.
    Qed.

    Polymorphic Lemma vec_Forall2_eq_rect_r :
      forall {n m} (mn : m = n) (va : Vec.t A n) (vb : Vec.t B m),
        Vec.Forall2 R va (eq_rect _ _ vb _ mn)
        <-> Vec.Forall2 R (eq_rect _ _ va _ (eq_sym mn)) vb.
    Proof using.
      intros n m nm va vb. depelim nm.
      reflexivity.
    Qed.
  End Forall2.
  
  Section Foldrightoflist.
    Polymorphic Variable f : A -> B -> B.
    Polymorphic Variable b : B.

    Polymorphic Lemma vec_fold_right_of_list : forall (l : list A),
        Vec.fold_right f (Vec.of_list l) b = List.fold_right f b l.
    Proof using.
      intro l; induction l as [| a l ih]; cbn; f_equal; auto.
    Qed.

    Polymorphic Lemma vec_fold_right_eq_rect : forall {n m} (nm : n = m) (v : Vec.t A n),
        Vec.fold_right f (eq_rect _ _ v _ nm) b = Vec.fold_right f v b.
    Proof using.
      intros n m nm v; depelim nm. reflexivity.
    Qed.
  End Foldrightoflist.

  Section Foldleftoflist.
    Polymorphic Variable f : B -> A -> B.

    Polymorphic Lemma vec_fold_left_of_list : forall (l : list A) (b : B),
        Vec.fold_left f b (Vec.of_list l) = List.fold_left f l b.
    Proof using.
      intro l; induction l as [| a l ih]; intro b; cbn; f_equal; auto.
    Qed.

    Polymorphic Lemma vec_fold_left_eq_rect : forall {n m} (nm : n = m) (v : Vec.t A n) (b : B),
        Vec.fold_left f b (eq_rect _ _ v _ nm) = Vec.fold_left f b v.
    Proof using.
      intros n m nm v b. depelim nm. reflexivity.
    Qed.
  End Foldleftoflist.
  
  Section mapoflist.
    Import List.ListNotations.
    Polymorphic Variable f : A -> B.

    Polymorphic Equations my_map_length : forall l : list A,
        length (List.map f l) = length l := {
        my_map_length []%list := eq_refl;
        my_map_length (_ :: t)%list := f_equal S (my_map_length t)
      }.

    Local Hint Resolve PeanoNat.Nat.eq_dec : core.

    Polymorphic Lemma vec_map_of_list : forall l : list A,
        Vec.map f (Vec.of_list l)
        = eq_rect _ _ (Vec.of_list (List.map f l)) _ (my_map_length l).
    Proof using.
      intro l; induction l as [| a l ih]; cbn.
      - rewrite <- Eqdep_dec.eq_rect_eq_dec by auto.
        reflexivity.
      - rewrite my_map_length_equation_2.
        rewrite map_subst_map, ih. reflexivity.
    Qed.

    Polymorphic Lemma vec_of_list_map : forall l : list A,
        Vec.of_list (List.map f l)
        = eq_rect
            _ _
            (Vec.map f (Vec.of_list l)) _
            (eq_sym (my_map_length l)).
    Proof using.
      intro l; induction l as [| a l ih]; cbn.
      - rewrite <- Eqdep_dec.eq_rect_eq_dec by auto.
        reflexivity.
      - rewrite my_map_length_equation_2.
        rewrite eq_sym_map_distr.
        rewrite map_subst_map, ih. reflexivity.
    Qed.
  End mapoflist.

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


Section Forall2flip.
  Polymorphic Universes a b.
  Polymorphic Context {A : Type@{a}} {B : Type@{b}}.
  
  Polymorphic Lemma vec_Forall2_flip :
    forall (R : A -> B -> Prop) {n} (va : Vec.t A n) (vb : Vec.t B n),
      Vec.Forall2 R va vb <-> Vec.Forall2 (fun b a => R a b) vb va.
  Proof using.
    intros R n va vb.
    do 2 rewrite vec_Forall2_forall.
    reflexivity.
  Qed.
End Forall2flip.

Section Forall3.
  Import Vec.VectorNotations.
  Local Open Scope vector_scope.
  
  Polymorphic Universes a b c.

  Section Forall3.
    Polymorphic Context {A : Type@{a}} {B : Type@{b}} {C : Type@{c}}.
    Polymorphic Variable R : A -> B -> C -> Prop.

    Polymorphic Inductive vec_Forall3 :
      forall {n}, Vec.t A n -> Vec.t B n -> Vec.t C n -> Prop :=
    | vec_Forall3_nil : vec_Forall3 [] [] []
    | vec_Forall3_cons {n} a b c (va : Vec.t A n) (vb : Vec.t B n) (vc : Vec.t C n) :
      R a b c -> vec_Forall3 va vb vc -> vec_Forall3 (a :: va) (b :: vb) (c :: vc).

    Polymorphic Derive Signature for vec_Forall3.

    Local Hint Constructors vec_Forall3 : core.
    Local Hint Constructors Vec.Forall2 : core.
    
    Polymorphic Lemma vec_Forall3_Forall2_12 :
      forall {n} (va : Vec.t A n) (vb : Vec.t B n) (vc : Vec.t C n),
        vec_Forall3 va vb vc
        <-> Vec.Forall2 (uncurry R) (vec_zip va vb) vc.
    Proof using.
      intros n va vb vc; split; intro h.
      - depind h.
        + rewrite vec_zip_equation_1; auto.
        + rewrite vec_zip_equation_2; auto.
      - funelim (vec_zip va vb); depelim vc; auto.
        rewrite vec_zip_equation_2 in h0.
        depelim h0. auto.
    Qed.

    Polymorphic Lemma vec_Forall3_forall : forall {n} (va : Vec.t A n) (vb : Vec.t B n) (vc : Vec.t C n),
        vec_Forall3 va vb vc <-> forall num, R (va [@ num]) (vb [@ num]) (vc [@ num]).
    Proof using.
      intros n va vb vc; split; intro h.
      - intro num. depind h; depelim num; cbn; auto.
      - generalize dependent vc.
        generalize dependent vb.
        depind va; intros vb vc H; depelim vb; depelim vc; auto.
        pose proof H Fin.F1 as H1; cbn in H1.
        constructor; auto.
        apply IHva. intro num.
        specialize H with (Fin.FS num); cbn in H.
        assumption.
    Qed.

    Local Hint Constructors Forall3 : core.
    
    Polymorphic Lemma vec_Forall3_to_list :
      forall {n} (va : Vec.t A n) (vb : Vec.t B n) (vc : Vec.t C n),
        Forall3 R (Vec.to_list va) (Vec.to_list vb) (Vec.to_list vc)
        <-> vec_Forall3 va vb vc.
    Proof using.
      intros n va vb vc; split; intro h.
      - generalize dependent vc.
        generalize dependent vb.
        depind va; intros vb vc H; depelim vb; depelim vc;
          cbn in *; inv H; auto.
      - depind h; cbn; auto.
    Qed.

    Local Hint Resolve PeanoNat.Nat.eq_dec : core.
    Local Hint Resolve Peano_dec.UIP_nat : core.
    
    Polymorphic Lemma vec_Forall3_of_list :
      forall la lb lc (hlenba : length lb = length la) (hlenca : length lc = length la),
        vec_Forall3
          (Vec.of_list la)
          (eq_rect _ _ (Vec.of_list lb) _ hlenba)
          (eq_rect _ _ (Vec.of_list lc) _ hlenca)
        <-> Forall3 R la lb lc.
    Proof using.
      intros la lb lc hba hca; split.
      - generalize dependent lc.
        generalize dependent lb.
        induction la as [| a la ih];
          intros [| b lb] hba [| c lc] hca h; cbn in *;
          try discriminate; auto.
        assert (length lb = length la) as hab by lia.
        assert (length lc = length la) as hac by lia.
        replace hba with (f_equal S hab) in h by auto.
        replace hca with (f_equal S hac) in h by auto.
        do 2 rewrite map_subst_map in h.
        depelim h. eauto.
      - intro h; induction h; cbn in *.
        + do 2 rewrite <- Eqdep_dec.eq_rect_eq_dec by auto; auto.
        + assert (length us = length ts) as hab by lia.
          assert (length vs = length ts) as hac by lia.
          replace hba with (f_equal S hab) by auto.
          replace hca with (f_equal S hac) by auto.
          do 2 rewrite map_subst_map. auto.
    Qed.

    Polymorphic Lemma vec_Forall3_eq_rect_l_to_mr :
      forall {n m} (nm : n = m) (va : Vec.t A n) (vb : Vec.t B m) (vc : Vec.t C m),
        vec_Forall3 (eq_rect _ _ va _ nm) vb vc
        <-> vec_Forall3
            va (eq_rect _ _ vb _ (eq_sym nm))
            (eq_rect _ _ vc _ (eq_sym nm)).
    Proof using.
      intros n m nm va vb vc.
      depelim nm. reflexivity.
    Qed.
    
    Polymorphic Lemma vec_Forall3_eq_rect_m_to_lr :
      forall {n m} (nm : n = m) (va : Vec.t A m) (vb : Vec.t B n) (vc : Vec.t C m),
        vec_Forall3 va (eq_rect _ _ vb _ nm) vc
        <-> vec_Forall3
            (eq_rect _ _ va _ (eq_sym nm)) vb
            (eq_rect _ _ vc _ (eq_sym nm)).
    Proof using.
      intros n m nm va vb vc.
      depelim nm. reflexivity.
    Qed.
    
    Polymorphic Lemma vec_Forall3_eq_rect_r_to_lm :
      forall {n m} (nm : n = m) (va : Vec.t A m) (vb : Vec.t B m) (vc : Vec.t C n),
        vec_Forall3 va vb (eq_rect _ _ vc _ nm)
        <-> vec_Forall3
            (eq_rect _ _ va _ (eq_sym nm))
            (eq_rect _ _ vb _ (eq_sym nm)) vc.
    Proof using.
      intros n m nm va vb vc.
      depelim nm. reflexivity.
    Qed.
  End Forall3.

  Local Hint Constructors vec_Forall3 : core.
  
  Section Forall3.
    Polymorphic Context {A : Type@{a}} {B : Type@{b}} {C : Type@{c}}.
  
    Polymorphic Lemma vec_Forall3_permute_12 :
      forall (R : A -> B -> C -> Prop) {n}
        (va : Vec.t A n) (vb : Vec.t B n) (vc : Vec.t C n),
        vec_Forall3 R va vb vc
        <-> vec_Forall3 (fun b a => R a b) vb va vc.
    Proof using.
      intros R n va vb vc; split; intro h; depind h; auto.
    Qed.
    
    Polymorphic Lemma vec_Forall3_permute_13 :
      forall (R : A -> B -> C -> Prop) {n}
        (va : Vec.t A n) (vb : Vec.t B n) (vc : Vec.t C n),
        vec_Forall3 R va vb vc
        <-> vec_Forall3 (fun c b a => R a b c) vc vb va.
    Proof using.
      intros R n va vb vc; split; intro h; depind h; auto.
    Qed.
    
    Polymorphic Lemma vec_Forall3_permute_23 :
      forall (R : A -> B -> C -> Prop) {n}
        (va : Vec.t A n) (vb : Vec.t B n) (vc : Vec.t C n),
        vec_Forall3 R va vb vc
        <-> vec_Forall3 (fun a c b => R a b c) va vc vb.
    Proof using.
      intros R n va vb vc; split; intro h; depind h; auto.
    Qed.
  End Forall3.
    
  Polymorphic Lemma vec_Forall3_Forall2_23 :
    forall {A : Type@{a}} {B : Type@{b}} {C : Type@{c}}
      (R : A -> B -> C -> Prop) {n}
      (va : Vec.t A n) (vb : Vec.t B n) (vc : Vec.t C n),
      vec_Forall3 R va vb vc
      <-> Vec.Forall2 (fun a => uncurry (R a)) va (vec_zip vb vc).
  Proof using.
    intros A B C R n va vb vc.
    rewrite vec_Forall3_permute_12.
    rewrite vec_Forall3_permute_23.
    rewrite vec_Forall3_Forall2_12.
    rewrite vec_Forall2_flip.
    do 2 rewrite vec_Forall2_forall.
    unfold uncurry.
    intuition; specialize H with m;
      do 2 let_destr_pair; assumption.
  Qed.
End Forall3.
