From Poulet4 Require Import
     P4cub.Syntax.AST
     P4cub.Syntax.Shift
     Utils.ForallMap
     Utils.VecUtil.
From Equations Require Import Equations.
Require Poulet4.Utils.ProdN.

Ltac pair_destr :=
  match goal with
  | h: (_,_) = (_,_) |- _ => inv h
  end.

Ltac conj_destr :=
  match goal with
    h: _ /\ _ |- _ => destruct h as [? ?]
  end.

Ltac let_destr_pair :=
  match goal with
    |- context [let (_,_) := ?a in _]
    => rewrite surjective_pairing with (p:=a); cbn
  end.

Section ShiftPairs.
  Import ProdN.ProdNNotations.
  Import Vec.VectorNotations.
  Local Open Scope prodn_scope.

  Polymorphic Universes a.
  
  Polymorphic Equations prodn_shift_pairs :
    forall {n : nat} {AS : Vec.t Type@{a} n},
      ProdN.t (Vec.map shifter AS) ->
      ProdN.t AS -> Vec.t (list Exp.t) n ->
      ProdN.t AS * Vec.t (list Exp.t) n := {
      prodn_shift_pairs [] [] []%vector := ([], []%vector);
      prodn_shift_pairs (f :: fs) (a :: p) (es :: ess)%vector :=
        let m := vec_sum $ Vec.map (length (A:=Exp.t)) ess in
        let '(p', v') := prodn_shift_pairs fs p ess in
        (f (length es) m a ::
           ProdN.map_uni2 0 (length es) fs p',
          (shift_list shift_exp 0 m es :: v')%vector)
    }.

  Polymorphic Lemma prodn_shift_pairs_inner_length :
    forall {n : nat} {AS : Vec.t Type@{a} n}
      (fs : ProdN.t (Vec.map shifter AS))
      (p : ProdN.t AS) (v : Vec.t (list Exp.t) n),
      Vec.map (length (A:=Exp.t)) (snd (prodn_shift_pairs fs p v))
      = Vec.map (length (A:=Exp.t)) v.
  Proof using.
    intros n AS fs p v.
    funelim (prodn_shift_pairs fs p v); unravel in *.
    - reflexivity.
    - rewrite prodn_shift_pairs_equation_2. cbn.
      let_destr_pair. unravel.
      rewrite shift_list_length.
      f_equal. assumption.
  Qed.

  Section ShiftCouple.
    Polymorphic Context {A : Type@{a}}.
    Variables fa : shifter A.

    Polymorphic Definition vec_shift_pairs
      {n : nat} (v : Vec.t A n) (ess : Vec.t (list Exp.t) n)
      : Vec.t A n * Vec.t (list Exp.t) n :=
      prod_map_fst ProdN.to_vec $
        prodn_shift_pairs
        (AS:=vec_rep n A) (ProdN.rep_param fa n) (ProdN.of_vec v) ess.

    Polymorphic Lemma vec_shift_pairs_nil :
      vec_shift_pairs []%vector []%vector = ([]%vector, []%vector).
    Proof using.
      unfold vec_shift_pairs; unravel.
      rewrite (ProdN.of_vec_equation_1 (A:=A)).
      rewrite prodn_shift_pairs_equation_1; cbn.
      rewrite ProdN.to_vec_equation_1.
      reflexivity.
    Qed.

    Polymorphic Lemma vec_shift_pairs_cons :
      forall {n} a (v : Vec.t A n) es (ess : Vec.t (list Exp.t) n),
        vec_shift_pairs (a :: v)%vector (es :: ess)%vector
        = ((fa (length es) (vec_sum (Vec.map (length (A:=Exp.t)) ess)) a ::
              Vec.map (fa 0 (length es)) (fst (vec_shift_pairs v ess)))%vector,
            (shift_list shift_exp 0 (vec_sum (Vec.map (length (A:=Exp.t)) ess)) es
               :: snd (vec_shift_pairs v ess))%vector).
    Proof using.
      intros n a v es ess.
      unfold vec_shift_pairs; unravel.
      rewrite ProdN.of_vec_equation_2, prodn_shift_pairs_equation_2.
      let_destr_pair.
      unravel. rewrite ProdN.to_vec_equation_2. f_equal. f_equal.
      rewrite <- ProdN.to_vec_map_uni2.
      reflexivity.
    Qed.

    Polymorphic Lemma vec_shift_pairs_inner_length : forall {n} (v : Vec.t A n) ess,
        Vec.map (length (A:=Exp.t)) (snd (vec_shift_pairs v ess))
        = Vec.map (length (A:=Exp.t)) ess.
    Proof using.
      intros n v ess.
      unfold vec_shift_pairs; unravel.
      rewrite snd_prod_map_fst, prodn_shift_pairs_inner_length.
      reflexivity.
    Qed.
    
    Polymorphic Definition shift_pairs
      (l : list (A * list Exp.t)) : list A * list (list Exp.t) :=
      let '(v,ess) := vec_unzip $ Vec.of_list l in
      prod_map_fst Vec.to_list $ prod_map_snd Vec.to_list $ vec_shift_pairs v ess.

    Polymorphic Lemma shift_pairs_nil : shift_pairs []%list = ([]%list,[]%list).
    Proof using.
      unfold shift_pairs; unravel.
      rewrite vec_unzip_equation_1.
      rewrite vec_shift_pairs_nil.
      reflexivity.
    Qed.

    Polymorphic Lemma shift_pairs_cons : forall (a : A) es l,
        shift_pairs ((a, es) :: l)%list
        = ((fa (length es) (list_sum (map (length (A:=Exp.t)) (map snd l))) a ::
              List.map (fa 0 (length es)) (fst (shift_pairs l)))%list,
            (shift_list shift_exp 0 (list_sum (map (length (A:=Exp.t)) (map snd l))) es
               :: snd (shift_pairs l))%list).
    Proof using.
      intros a es l.
      unfold shift_pairs; unravel.
      rewrite vec_unzip_equation_2.
      repeat let_destr_pair.
      rewrite vec_shift_pairs_cons. unravel.
      do 2 rewrite Vec.to_list_cons.
      rewrite Vec.to_list_map.
      rewrite fst_prod_map_fst, snd_prod_map_fst,
        fst_prod_map_snd, snd_prod_map_snd.
      rewrite vec_unzip_correct; simpl.
      rewrite Vec.map_map, List.map_map, vec_map_of_list, vec_sum_eq_rect.
      unfold vec_sum,list_sum. rewrite vec_fold_right_of_list.
      reflexivity.
    Qed.

    Polymorphic Lemma shift_pairs_lengths : forall l,
        length (fst (shift_pairs l)) = length l
        /\ length (snd (shift_pairs l)) = length l.
    Proof using.
      intro l; unfold shift_pairs; unravel.
      let_destr_pair.
      rewrite fst_prod_map_fst, snd_prod_map_fst,
        fst_prod_map_snd, snd_prod_map_snd.
      do 2 rewrite Vec.length_to_list.
      split; reflexivity.
    Qed.

    Polymorphic Lemma shift_pairs_inner_length : forall l,
        map (length (A:=Exp.t)) (snd (shift_pairs l))
        = map (length (A:=Exp.t)) (map snd l).
    Proof using.
      intro l. unfold shift_pairs; unravel.
      rewrite vec_unzip_correct, snd_prod_map_fst, snd_prod_map_snd.
      rewrite map_to_list, vec_shift_pairs_inner_length.
      do 2 rewrite <- map_to_list.
      rewrite Vec.to_list_of_list_opp. reflexivity.
    Qed.

    Polymorphic Variable lifta : A -> A * list Exp.t.
    
    Polymorphic Definition lift_A_list (l : list A) : list A * list Exp.t :=
      prod_map_snd (List.concat (A:=Exp.t)) $ shift_pairs $ List.map lifta l.

    Polymorphic Definition lift_A_list_length : forall l,
        length (fst (lift_A_list l)) = length l.
    Proof using.
      intro l; unfold lift_A_list; unravel.
      rewrite fst_prod_map_snd,
        (proj1 (shift_pairs_lengths (map lifta l))),
        map_length.
      reflexivity.
    Qed.

    Polymorphic Variable LiftA : A -> A -> list Exp.t -> Prop.
    
    Polymorphic Definition Lift_A_list (l l' : list A) (es : list Exp.t) : Prop :=
      exists la ess,
        Forall3 LiftA l la ess
        /\ l' = fst (shift_pairs (combine la ess))
        /\ es = List.concat (A:=Exp.t) (snd (shift_pairs (combine la ess))).

    Polymorphic Hypothesis LiftA_lifta : forall a a' es,
        LiftA a a' es -> lifta a = (a', es).

    Polymorphic Remark Forall3_LiftA_map_lifta : forall l l' ess,
        Forall3 LiftA l l' ess -> map lifta l = combine l' ess.
    Proof using A LiftA LiftA_lifta lifta.
      intros l l' ess h.
      induction h; cbn; f_equal; auto.
    Qed.
    
    Polymorphic Lemma Lift_A_list_lift_A_list : forall l l' es,
        Lift_A_list l l' es -> lift_A_list l = (l',es).
    Proof using A LiftA LiftA_lifta lifta.
      intros l l' es (la & ess & hLift & hl' & hes'); subst.
      unfold lift_A_list; unravel.
      apply Forall3_LiftA_map_lifta in hLift.
      rewrite hLift.
      apply injective_projections.
      - rewrite fst_prod_map_snd; reflexivity.
      - rewrite snd_prod_map_snd; reflexivity.
    Qed.

    Polymorphic Hypothesis lifta_LiftA : forall a,
        LiftA a (fst (lifta a)) (snd (lifta a)).

    Polymorphic Lemma lift_A_list_Lift_A_list : forall l,
        Lift_A_list l (fst (lift_A_list l)) (snd (lift_A_list l)).
    Proof using.
      intro l. unfold Lift_A_list.
      exists (map fst (map lifta l)), (map snd (map lifta l)).
      rewrite sublist.combine_eq.
      split.
      - do 2 rewrite <- Forall3_map_23. admit.
      - unfold lift_A_list; unravel.
        rewrite fst_prod_map_snd, snd_prod_map_snd.
        split; reflexivity.
    Qed.
        
    
    Polymorphic Context {B : Type@{a}}.
    Variable fb : shifter B.
    
    Polymorphic Hypothesis fa_0 : forall c a, fa c 0 a = a.
    Polymorphic Hypothesis fb_0 : forall c b, fb c 0 b = b.

    Local Hint Rewrite shift_exp_0 : core.
    Local Hint Resolve shift_exp_0 : core.
    Local Hint Rewrite PeanoNat.Nat.add_0_r : core.
    Local Hint Rewrite fa_0 : core.
    Local Hint Rewrite fb_0 : core.
    Local Hint Rewrite (@shift_list_0 Exp.t) : core.
    
    Polymorphic Lemma prodn_shift_pairs_single : forall a es,
        prodn_shift_pairs (AS:=[A]%vector) (fa :: []) (a :: []) [es]%vector
        = (a :: [],[es]%vector).
    Proof using A fa fa_0.
      intros; cbn.
      rewrite prodn_shift_pairs_equation_2; unravel.
      rewrite prodn_shift_pairs_equation_1; unravel.
      rewrite ProdN.map_uni2_equation_1.
      autorewrite with core. cbn.
      rewrite shift_list_0 by eauto.
      reflexivity.
    Qed.

    Polymorphic Lemma prodn_shift_pairs_couple :
      forall a b esa esb,
        prodn_shift_pairs
          (AS := [B; A]%vector)
          (fb :: fa :: []) (b :: a :: []) [esb ; esa]%vector
        = (fb (length esb) (length esa) b :: fa 0 (length esb) a :: [],
            [shift_list shift_exp 0 (length esa) esb; esa]%vector).
    Proof using A fa fb fa_0 fb_0.
      intros a b esa esb.
      rewrite prodn_shift_pairs_equation_2. cbn.
      rewrite prodn_shift_pairs_single.
      autorewrite with core. f_equal.
    Qed.

    Polymorphic Definition shift_couple
      (a : A) (b : B) (esa esb : list Exp.t) : A * B * list Exp.t :=
      let '(ba, ess) :=
        prodn_shift_pairs
          (AS := [B; A]%vector)
          (fb :: fa :: [])
          (b :: a :: [])
          [esb ; esa]%vector in
      (ProdN.nth (Fin.FS Fin.F1) ba,
        ProdN.hd ba, Vec.hd ess).

    Polymorphic Lemma shift_couple_length : forall a b esa esb,
        length (snd (shift_couple a b esa esb)) = length esb.
    Proof using.
      intros a b esa esb.
      unfold shift_couple.
      pose proof
        prodn_shift_pairs_inner_length
        (AS := [B; A]%vector)
        (fb :: fa :: [])
        (b :: a :: [])
        [esb ; esa]%vector as h.
      let_destr_pair.
      cbn in *.
      apply f_equal with (f:=Vec.hd) in h.
      rewrite vec_hd_map in h.
      assumption.
    Qed.
    
    Polymorphic Lemma shift_couple_spec : forall a b esa esb,
        fst (fst (shift_couple a b esa esb))
        = fa 0 (length esb) a
        /\ snd (fst (shift_couple a b esa esb))
          = fb (length esb) (length esa) b
        /\ snd (shift_couple a b esa esb)
          = shift_list shift_exp 0 (length esa) esb.
    Proof using A fa fb fa_0 fb_0.
      intros a b esa esb.
      destruct (shift_couple a b esa esb) as [[a' b'] esb'] eqn:h.
      unfold shift_couple in h.
      rewrite prodn_shift_pairs_couple in h.
      inv h. unravel. auto.
    Qed.

    Context {C : Type@{a}}.
    Variable fc : shifter C.

    Polymorphic Hypothesis fc_0 : forall ct c, fb ct 0 c = c.
    
    Polymorphic Hypothesis fa_add
      : forall m n a, fa 0 m (fa 0 n a) = fa 0 (m + n) a.

    Local Hint Rewrite fc_0 : core.
    Local Hint Rewrite fa_add : core.
    
    Polymorphic Lemma prodn_shift_pairs_triple :
      forall a b c esa esb esc,
        prodn_shift_pairs
          (AS:=[C; B; A]%vector)
          (fc :: fb :: fa :: [])
          (c :: b :: a :: [])
          [esc; esb; esa]%vector
        = (fc (length esc) (length esb + length esa) c ::
             fb 0 (length esc) (fb (length esb) (length esa) b) ::
             fa 0 (length esc + length esb) a :: [],
            [shift_list shift_exp 0 (length esb + length esa) esc;
             shift_list shift_exp 0 (length esa) esb; esa]%vector).
    Proof using A B C fa fa_0 fa_add fb fb_0 fc.
      intros a b c esa esb esc.
      rewrite prodn_shift_pairs_equation_2. cbn.
      rewrite prodn_shift_pairs_couple.
      rewrite ProdN.map_uni2_equation_2
        with (v := [A]%vector) (f := fb) (fs := fa :: []).
      rewrite ProdN.map_uni2_equation_2  with (v := []%vector) (f := fa) (fs := []).
      rewrite ProdN.map_uni2_equation_1.
      autorewrite with core. reflexivity.
    Qed.

    Polymorphic Definition shift_triple
      (a : A) (b : B) (c : C) (esa esb esc : list Exp.t)
      : A * B * C * list Exp.t * list Exp.t :=
      let '(cba, ess) :=
        prodn_shift_pairs
          (AS:=[C; B; A]%vector)
          (fc :: fb :: fa :: [])
          (c :: b :: a :: [])
          [esc; esb; esa]%vector in
      (ProdN.nth (Fin.FS $ Fin.FS Fin.F1) cba,
        ProdN.nth (Fin.FS Fin.F1) cba,
        ProdN.hd cba, Vec.nth ess (Fin.FS Fin.F1), Vec.hd ess).

    Polymorphic Lemma shift_triple_lengths : forall a b c esa esb esc,
        length (snd (fst (shift_triple a b c esa esb esc))) = length esb
        /\ length (snd (shift_triple a b c esa esb esc)) = length esc.
    Proof using.
      intros a b c esa esb esc.
      unfold shift_triple.
      pose proof prodn_shift_pairs_inner_length
        (AS:=[C; B; A]%vector)
        (fc :: fb :: fa :: [])
        (c :: b :: a :: [])
        [esc; esb; esa]%vector as h.
      let_destr_pair.
      pose proof f_equal Vec.hd h as hhd.
      pose proof f_equal (fun v => Vec.nth v (Fin.FS Fin.F1)) h as hnth.
      cbn in *. rewrite vec_hd_map in hhd.
      rewrite Vec.nth_map with (p2:=Fin.FS Fin.F1) in hnth by reflexivity.
      split; assumption.
    Qed.
    
    Polymorphic Lemma shift_triple_spec :
      forall a b c esa esb esc,
        fst (fst (fst (fst (shift_triple a b c esa esb esc))))
        = fa 0 (length esc + length esb) a
        /\ snd (fst (fst (fst (shift_triple a b c esa esb esc))))
          = fb 0 (length esc) (fb (length esb) (length esa) b)
        /\ snd (fst (fst (shift_triple a b c esa esb esc)))
          = fc (length esc) (length esb + length esa) c
        /\ snd (fst (shift_triple a b c esa esb esc))
          = shift_list shift_exp 0 (length esa) esb
        /\ snd (shift_triple a b c esa esb esc)
          = shift_list shift_exp 0 (length esb + length esa) esc.
    Proof using A B C fa fa_0 fa_add fb fb_0 fc.
      intros a b c esa esb esc.
      destruct (shift_triple a b c esa esb esc) as [[[[a' b'] c'] esb'] esc'] eqn:h.
      unfold shift_triple in h.
      rewrite prodn_shift_pairs_triple in h.
      unravel in *. inv h. auto.
    Qed.
  End ShiftCouple.
End ShiftPairs.
