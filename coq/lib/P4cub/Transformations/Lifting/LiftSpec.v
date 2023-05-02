Require Export Coq.Lists.List
  Coq.Arith.PeanoNat
  Poulet4.Utils.ForallMap
  Poulet4.P4cub.Syntax.Syntax
  Poulet4.P4cub.Syntax.Shift
  Poulet4.P4cub.Transformations.Lifting.Statementize
  Poulet4.P4cub.Transformations.Lifting.LiftList
  Poulet4.Utils.VecUtil.
Import ListNotations Nat.
Require Poulet4.Utils.ProdN.
From Equations Require Import Equations.

Section RelateDeclList.
  Polymorphic Universes a b.
  
  Polymorphic Context {A : Type@{a}} {B : Type@{b}}.
  Polymorphic Variable R : list A -> B -> A -> Prop.
  Polymorphic Variable l : list A.
  
  Polymorphic Inductive relate_decl_list : list B -> list A -> Prop :=
  | relate_decl_list_nil :
    relate_decl_list [] []
  | relate_decl_list_cons hb ha tb ta :
    R (ta ++ l) hb ha ->
    relate_decl_list tb ta ->
    relate_decl_list (hb :: tb) (ha :: ta).

  Polymorphic Lemma relate_decl_list_length : forall lb la,
      relate_decl_list lb la -> length lb = length la.
  Proof using.
    intros lb la h; induction h; cbn; auto.
  Qed.

  Polymorphic Hypothesis Rdet : forall la b a a',
      R la b a -> R la b a' -> a = a'.

  Polymorphic Lemma relate_decl_list_det : forall bs as1 as2,
      relate_decl_list bs as1 -> relate_decl_list bs as2 -> as1 = as2.
  Proof using A B R Rdet l.
    intros bs as1 as2 h1; generalize dependent as2;
      induction h1; intros as2 h2; inv h2; f_equal; eauto.
    pose proof IHh1 _ H4 as ?; subst. eauto.
  Qed.
End RelateDeclList.

Section RelateDeclListApp.
  Polymorphic Universes a b.
  Polymorphic Context {A : Type@{a}} {B : Type@{b}}.

  Local Hint Constructors relate_decl_list : core.
  
  Polymorphic Lemma pred_decl_list : forall (P : A -> Prop) (b : B) (bs : list B) (l : list A),
      relate_decl_list
        (fun _ a _ => P a) bs l (repeat b (length l))
      <-> Forall P l.
  Proof using.
    intros P b bs l; split; intros h;
      induction l as [| a l ih]; inv h; cbn; auto.
  Qed.
  
  Polymorphic Variable R : list A -> B -> A -> Prop.
  Polymorphic Variable shiftB : shifter B.

  Polymorphic Hypothesis shift_preserves_R : forall as1 as2 as3 a b,
      R (as1 ++ as3) b a ->
      R (as1 ++ as2 ++ as3) (shiftB (length as1) (length as2) b) a.

  Polymorphic Variable l : list A.

  Polymorphic Lemma relate_decl_list_app : forall bs1 bs2 as1 as2,
      relate_decl_list R l bs1 as1 ->
      relate_decl_list R l bs2 as2 ->
      relate_decl_list R l (shift_list shiftB 0 (length bs1) bs2 ++ bs1) (as2 ++ as1).
  Proof using A B R shift_preserves_R l.
    intros bs1 bs2 as1 as2 h1 h2.
    generalize dependent as1.
    generalize dependent bs1.
    induction h2; intros bs1 as1 h1; cbn; auto.
    constructor; auto. rewrite <- app_assoc.
    rewrite (relate_decl_list_length _ _ _ _ h1).
    rewrite (relate_decl_list_length _ _ _ _ h2).
    eauto.
  Qed.
End RelateDeclListApp.

Section RelateDeclListProdN.
  Polymorphic Universes a b.
  Polymorphic Context {A : Type@{a}}.
  Polymorphic Variable R_exp : list A -> Exp.t -> A -> Prop.
  Polymorphic Hypothesis shift_preserves_R_exp : forall as1 as2 as3 a e,
      R_exp (as1 ++ as3) e a ->
      R_exp (as1 ++ as2 ++ as3) (shift_exp (length as1) (length as2) e) a.
  Polymorphic Variable l : list A.
  
  (*Polymorphic Lemma relate_decl_prodn_shift_pairs :
    forall {n} {v : Vec.t Type@{b} n}
      (shifts : ProdN.t (Vec.map shifter v))
      (Rs : ProdN.t (Vec.map (fun B => list A -> B -> A -> Prop) v)),
      (forall (as1 as2 as3 : list A) (p : ProdN.t) (va : Vec.t A n),
          ProdN.relate_uni1 (as1 ++ as3) Rs p va ->
          ProdN.relate_uni1
            (as1 ++ as2 ++ as3)
            Rs (ProdN.map_uni2 (length as1) (length as2) shiftB p) va) ->
      forall (p : ProdN.t v) (ess : Vec.t (list Exp.t) n) (vas ass : Vec.t (list A) n),
        ProdN.relate_uni1
        ProdN.relate_middle R (Vec.map (fun a => a ++ l) vas p vs ->
        Vec.Forall2 (relate_decl_list R_exp l) ess ass ->
        relate_decl_list R l
          (Vec.concat (snd (prodn_shift_pairs shifts p ess)))
          (Vec.concat ass).*)
      
End RelateDeclListProdN.

Section RelateExprDeclList.
  Import List.ListNotations.
  Import Vec.VectorNotations.
  
  Polymorphic Universes a b.
  Polymorphic Context {A : Type@{a}} {B : Type@{b}}.
  Polymorphic Variable shiftB : shifter B.
  Polymorphic Variable R : list A -> B -> A -> Prop.
  Polymorphic Hypothesis shift_preserves_R : forall as1 as2 as3 b a,
      R (as1 ++ as3) b a ->
      R (as1 ++ as2 ++ as3) (shiftB (length as1) (length as2) b) a.

  Local Hint Constructors Vec.Forall2 : core.
  
  Polymorphic Lemma shift_preserves_R_vec_Forall2 :
    forall (as1 as2 as3 : list A) {n} (bs : Vec.t B n) (vs : Vec.t A n),
      Vec.Forall2 (R (as1 ++ as3)) bs vs ->
      Vec.Forall2 (R (as1 ++ as2 ++ as3)) (Vec.map (shiftB (length as1) (length as2)) bs) vs.
  Proof using A B R shiftB shift_preserves_R.
    intros as1 as2 as3 n bs vs h.
    depind h; cbn; auto.
  Qed.

  Local Hint Resolve shift_preserves_R_vec_Forall2 : core.
  Local Hint Resolve Peano_dec.UIP_nat : core.

  Polymorphic Lemma shift_preserves_R_Forall2 :
    forall (as1 as2 as3 : list A) (bs : list B) (vs : list A),
      Forall2 (R (as1 ++ as3)) bs vs ->
      Forall2 (R (as1 ++ as2 ++ as3)) (List.map (shiftB (length as1) (length as2)) bs) vs.
  Proof using A B R shiftB shift_preserves_R.
    intros as1 as2 as3 bs vs h.
    rewrite Forall2_flip in h |- *.
    pose proof sublist.Forall2_length h as hlen.
    symmetry in hlen.
    rewrite <- vec_Forall2_of_list with (hlen:=hlen) in h.
    pose proof map_length (shiftB (length as1) (length as2)) bs as hlenmap.
    rewrite hlen in hlenmap.
    rewrite <- vec_Forall2_of_list with (hlen:=hlenmap).
    rewrite <- vec_Forall2_flip in h |- *.
    rewrite vec_of_list_map.
    rewrite rew_compose.
    rewrite map_subst.
    replace (Logic.eq_trans (Logic.eq_sym (my_map_length (shiftB (length as1) (length as2)) bs)) hlenmap)
      with hlen by auto. auto.
  Qed.
  
  Polymorphic Variable R_exp : list A -> Exp.t -> A -> Prop.
  Polymorphic Hypothesis shift_preserves_R_exp : forall as1 as2 as3 e a,
      R_exp (as1 ++ as3) e a ->
      R_exp (as1 ++ as2 ++ as3) (shift_exp (length as1) (length as2) e) a.
  Polymorphic Variable l : list A.
  
  Local Hint Resolve relate_decl_list_app : core.
  Local Hint Constructors relate_decl_list : core.
  
  Polymorphic Lemma vec_shift_pairs_relate_snd :
    forall {n} (bs : Vec.t B n) (ess : Vec.t (list Exp.t) n) (ass : Vec.t (list A) n),
      Vec.Forall2 (relate_decl_list R_exp l) ess ass ->
      relate_decl_list R_exp l
        (vec_concat_list (snd (vec_shift_pairs shiftB bs ess)))
        (vec_concat_list ass).
  Proof using A B shiftB R_exp l shift_preserves_R_exp.
    intros n bs ess ass h; generalize dependent bs.
    depind h; intro bs; depelim bs.
    - rewrite vec_shift_pairs_nil; cbn; auto.
    - rewrite vec_shift_pairs_cons; cbn.
      pose proof IHh bs as ih; clear IHh.
      assert (vec_sum (Vec.map (length (A:=Exp.t)) v1)
              = length (vec_concat_list (snd (vec_shift_pairs shiftB bs v1)))) as hlen.
      { unfold vec_sum.
        rewrite length_vec_concat_list.
        rewrite vec_shift_pairs_inner_length.
        reflexivity. }
      rewrite hlen; auto.
  Qed.

  Polymorphic Lemma vec_shift_pairs_relate_fst :
    forall {n} (bs : Vec.t B n) (ess : Vec.t (list Exp.t) n) (vs : Vec.t A n) (ass : Vec.t (list A) n),
      vec_Forall3 (fun vs e v => R (vs ++ l) e v) ass bs vs ->
      Vec.Forall2 (relate_decl_list R_exp l) ess ass ->
      Vec.Forall2
        (R (vec_concat_list ass ++ l))
        (fst (vec_shift_pairs shiftB bs ess)) vs.
  Proof using A B R R_exp l shiftB shift_preserves_R shift_preserves_R_exp.
    intros n bs ess vs ass hf3 hf2.
    generalize dependent ess.
    depind hf3; intros ess hf2; depelim hf2.
    - rewrite vec_shift_pairs_nil; cbn; auto.
    - rewrite vec_shift_pairs_cons; simpl.
      rewrite vec_concat_list_cons.
      rewrite <- app_assoc.
      constructor; auto.
      + unfold vec_sum.
        apply vec_shift_pairs_relate_snd with (bs:=vb) in hf2.
        apply relate_decl_list_length in H0,hf2.
        rewrite length_vec_concat_list in hf2.
        rewrite vec_shift_pairs_inner_length in hf2.
        rewrite <- length_vec_concat_list in hf2.
        rewrite <- length_vec_concat_list,hf2,H0. auto.
      + apply relate_decl_list_length in H0.
        rewrite H0.
        apply IHhf3 in hf2.
        apply shift_preserves_R_vec_Forall2 with
          (as1 := []%list) (as2 := a) (as3 := (vec_concat_list va ++ l)%list).
        assumption.
  Qed.
  
  Polymorphic Lemma shift_pairs_relate_snd : forall (ess : list (B * list Exp.t)) ass,
      Forall2 (relate_decl_list R_exp l) (map snd ess) ass ->
      relate_decl_list R_exp l
        (concat (snd (shift_pairs shiftB ess)))
        (concat ass).
  Proof using A B shiftB R_exp l shift_preserves_R_exp.
    intros ess ass h.
    unfold shift_pairs; unravel.
    let_destr_pair.
    rewrite snd_prod_map_fst,snd_prod_map_snd.
    rewrite vec_unzip_correct; cbn.
    rewrite <- Vec.to_list_of_list_opp with (l:=ass).
    do 2 rewrite concat_vec_to_list.
    pose proof sublist.Forall2_length h as hlen.
    rewrite map_length in hlen.
    symmetry in hlen.
    unfold vec_concat_list at 2.
    rewrite <- vec_fold_right_eq_rect with (nm:=hlen) (v:=Vec.of_list ass).
    apply vec_shift_pairs_relate_snd.
    rewrite vec_map_of_list, vec_Forall2_eq_rect_l, rew_compose, vec_Forall2_of_list.
    assumption.
  Qed.

  Polymorphic Lemma shift_pairs_relate_fst : forall es ess vs vss,
      length es = length ess ->
      Forall3 (fun vs e v => R (vs ++ l) e v) vss es vs ->
      Forall2 (relate_decl_list R_exp l) ess vss ->
      Forall2
        (R (concat vss ++ l))
        (fst (shift_pairs shiftB (combine es ess))) vs.
  Proof using A B shiftB R R_exp l shift_preserves_R shift_preserves_R_exp.
    intros es ess vs vss hl hes hess.
    unfold shift_pairs; unravel; let_destr_pair.
    rewrite fst_prod_map_fst, fst_prod_map_snd.
    rewrite vec_unzip_correct; cbn.
    rewrite <- Vec.to_list_of_list_opp with (l:=vss).
    rewrite <- Vec.to_list_of_list_opp with (l:=vs).
    rewrite concat_vec_to_list.
    assert (hlen : length vs = length (combine es ess)
                   /\ length vss = length (combine es ess)).
    { apply Forall3_length23 in hes.
      apply sublist.Forall2_length in hess.
      rewrite combine_length. lia. }
    destruct hlen as [hlenvs hlenvss].
    rewrite vec_to_list_fold_right with (v:=Vec.of_list vs).
    rewrite <- vec_fold_right_eq_rect with (nm:=hlenvs) (v:=Vec.of_list vs).
    rewrite <- vec_to_list_fold_right.
    unfold vec_concat_list.
    rewrite <- vec_fold_right_eq_rect with (nm:=hlenvss) (v:=Vec.of_list vss).
    rewrite <- Vec.to_list_Forall2.
    apply vec_shift_pairs_relate_fst.
    - rewrite vec_map_of_list, vec_Forall3_eq_rect_l_to_mr.
      do 2 rewrite rew_compose.
      rewrite vec_Forall3_of_list.
      rewrite map_fst_combine by assumption.
      assumption.
    - rewrite vec_map_of_list, vec_Forall2_eq_rect_l,
        rew_compose, vec_Forall2_of_list.
      rewrite map_snd_combine by assumption.
      assumption.
  Qed.

  Polymorphic Universe c.
  Polymorphic Context {C : Type@{c}}.
  Polymorphic Variable shiftC : shifter C.
  Polymorphic Variable Q : list A -> C -> A -> Prop.
  Polymorphic Hypothesis shift_preserves_Q : forall as1 as2 as3 c a,
      Q (as1 ++ as3) c a ->
      Q (as1 ++ as2 ++ as3) (shiftC (length as1) (length as2) c) a.

  Polymorphic Lemma shift_couple_relate_decl_list : forall b c esb esc asb asc,
      relate_decl_list R_exp l esb asb ->
      relate_decl_list R_exp l esc asc ->
      relate_decl_list
        R_exp l
        (snd (shift_couple shiftB shiftC b c esb esc) ++ esb)
        (asc ++ asb).
  Proof using A B C R_exp l shiftB shiftC shift_preserves_R_exp.
    intros b c esb esc asb asc hb hc.
    unfold shift_couple.
    do 2 rewrite prodn_shift_pairs_equation_2.
    rewrite prodn_shift_pairs_equation_1. unravel. cbn.
    rewrite add_0_r. auto.
  Qed.

  Polymorphic Lemma shift_couple_relate_couple : forall b c esb esc asb asc vb vc,
      relate_decl_list R_exp l esb asb ->
      relate_decl_list R_exp l esc asc ->
      R (asb ++ l) b vb ->
      Q (asc ++ l) c vc ->
      R (asc ++ asb ++ l) (fst (fst (shift_couple shiftB shiftC b c esb esc))) vb
      /\ Q (asc ++ asb ++ l) (snd (fst (shift_couple shiftB shiftC b c esb esc))) vc.
  Proof using A B C Q R R_exp l shiftB shiftC shift_preserves_Q shift_preserves_R.
    intros b c esb esc asb asc vb vc hesb hesc hb hc.
    unfold shift_couple.
    do 2 rewrite prodn_shift_pairs_equation_2.
    rewrite prodn_shift_pairs_equation_1. unravel. cbn.
    rewrite add_0_r.
    rewrite ProdN.nth_equation_2, ProdN.hd_equation_1.
    rewrite ProdN.map_uni2_equation_2 with (f:=shiftB).
    rewrite ProdN.nth_equation_1.
    apply relate_decl_list_length in hesb,hesc.
    rewrite hesb,hesc.
    split; auto.
    apply shift_preserves_R with
      (as1:=asb) (as2:=[]%list) (as3:=l) in hb.
    apply shift_preserves_R with
      (as1:=[]%list) (as2:=asc) (as3:=(asb ++ l)%list) in hb.
    assumption.
  Qed.
End RelateExprDeclList.
