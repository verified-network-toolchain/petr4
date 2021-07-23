Require Export Poulet4.P4cub.Util.Utiliser.

(** * Definitions and Lemmas Regarding Fields *)

Module Field.
  Section FieldTypes.
    Variables K V : Type. (** key & value types. *)

    (** Field type. *)
    Definition f : Type := K * V.

    (** Fields. *)
    Definition fs : Type := list f.
  End FieldTypes.

  Section FieldLibrary.
    Definition key {K V : Type} : f K V -> K := fst.

    Definition value {K V : Type} : f K V -> V := snd.

    Definition keys {K V : Type} : fs K V -> list K := List.map key.

    Definition values {K V : Type} : fs K V -> list V := List.map value.

    Lemma key_value : forall {K V : Type} (fld : f K V),
        (key fld, value fld) = fld.
    Proof. intros K V []; reflexivity. Qed.

    Lemma keys_values : forall {K V : Type} (flds : fs K V),
        combine (keys flds) (values flds) = flds.
    Proof.
      induction flds as [| [? ?] ? ?]; unravel;
      try f_equal; assumption.
    Qed.

    (** Predicate on a field's data. *)
    Definition predf_data {K T : Type} (P : T -> Prop) : f K T -> Prop := P ∘ snd.
    (**[]*)

    (** Predicate over every data in fields. *)
    Definition predfs_data {K T : Type} (P : T -> Prop) : fs K T -> Prop :=
      Forall (predf_data P).
    (**[]*)

    Lemma predfs_data_map : forall {K V : Type} (P : V -> Prop) (flds : fs K V),
        predfs_data P flds <-> Forall P (map snd flds).
    Proof.
      induction flds as [| [k v] flds IHflds];
        unravel; split; intros H; inv H; constructor;
          unfold predfs_data, predf_data, "∘" in *;
          unravel in *; intuition.
    Qed.

    (** Filter. *)
    Definition filter {K U : Type} (pred : U -> bool) : fs K U -> fs K U :=
      List.filter (pred ∘ snd).
    (**[]*)

    (** Map. *)
    Definition map {K U V : Type} (f : U -> V) : fs K U -> fs K V :=
      List.map (fun '(x,u) => (x, f u)).
    (**[]*)

    Lemma map_fst : forall {K U V : Type} (g : U -> V) (flds : fs K U),
        List.map fst (map g flds) = List.map fst flds.
    Proof.
      intros; induction flds as [| [? ?] ? ?]; unravel; auto.
      rewrite IHflds; reflexivity.
    Qed.

    Lemma map_snd : forall {K U V : Type} (g : U -> V) (flds : fs K U),
        List.map snd (map g flds) = List.map (g ∘ snd) flds.
    Proof.
      intros; induction flds as [| [? ?] ? ?]; unravel in *; auto.
      rewrite IHflds; reflexivity.
    Qed.

    (** Fold. *)
    Definition fold {K U V : Type} (f : K -> U -> V -> V)
               (fds : fs K U) (init : V) : V :=
      List.fold_right (fun '(x,u) acc => f x u acc) init fds.
    (**[]*)

    Fixpoint find_value {K V : Type} (f : K -> bool) (fds : fs K V) : option V :=
      match fds with
      | [] => None
      | (k, v) :: fds => if f k then Some v else find_value f fds
      end.
    
    Section GetUpdate.
      Context {K U : Type}.
      Context {keq : K -> K -> Prop}.
      Context `{Equivalence K keq}.
      Context `{EqDec K keq}.

      (** Member access. *)
      Fixpoint get (k : K) (fds : fs K U) : option U :=
        match fds with
        | []            => None
        | (k',u') :: fds => if equiv_dec k k' then Some u'
                          else get k fds
        end.
      (**[]*)

      Fixpoint get_index_rec (k: K) (fds : fs K U) (current : nat) : option nat :=
        match fds with 
        | [] => None
        | (k',u') :: fds => if equiv_dec k k' then Some (current)
                            else get_index_rec k fds (S current)
        end. 
      Definition get_index (k: K) (fds : fs K U) : option nat := 
        get_index_rec k fds 0.
      (** Member update. *)
      Fixpoint update (k : K) (u : U) (fds : fs K U) : fs K U :=
        match fds with
        | [] => []
        | (k',u') :: fds => (k', if equiv_dec k k' then u else u') :: update k u fds
        end.
      (**[]*)
    End GetUpdate.

    Section FieldRelations.
      Context {K U V : Type}.
      Context {keq : K -> K -> Prop}.
      Context `{HK : Equivalence K keq}.
      Variable R : U -> V -> Prop.

      (** Relation betwixt two field instances. *)
      Definition relf : f K U -> f K V -> Prop :=
        fun u v => equiv (fst u) (fst v) /\ R (snd u) (snd v).
      (**[]*)

      (** Relation between two instances of fields. *)
      Definition relfs : fs K U -> fs K V -> Prop := Forall2 relf.
      (**[]*)

      Ltac inv_prod_eq :=
        match goal with
        | H: (_,_) = (_,_) |- _ => inv H
        end.
      (**[]*)

      Ltac let_pair_simpl :=
        match goal with
        | H: context [let (_,_) := ?x in _]
          |- context [let (_,_) := ?x in _] => destruct x as [? ?] eqn:?
        | H: context [let (_,_) := ?x in _] |- _ => destruct x as [? ?] eqn:?
        | |- context [let (_,_) := ?x in _] => destruct x as [? ?] eqn:?
        | H: (_,_) = (_,_) |- _ => inv H
        end.
      (**[]*)

      Lemma relfs_split : forall us vs,
          relfs us vs ->
          let (xus, uus) := split us in
          let (xvs, vvs) := split vs in
          Forall2 keq xus xvs /\ Forall2 R uus vvs.
      Proof.
        intros us vs H; induction H;
        unfold relf in *; unravel in *; intuition.
        destruct x as [xu u]; destruct y as [xv v]; simpl in *.
        repeat let_pair_simpl. intuition.
      Qed.

      Lemma combine_relfs : forall xus xvs uus vvs,
          Forall2 keq xus xvs -> Forall2 R uus vvs ->
          let us := combine xus uus in
          let vs := combine xvs vvs in
          relfs us vs.
      Proof.
        intros xus xvs uus vvs Hu Hv;
        generalize dependent vvs; generalize dependent uus.
        induction Hu; intros uus vvs Hv; inv Hv;
        unfold relfs, relf in *; unravel in *; intuition.
      Qed.

      Lemma relfs_split_iff : forall us vs,
          let (xus, uus) := split us in
          let (xvs, vvs) := split vs in
          relfs us vs <-> Forall2 keq xus xvs /\ Forall2 R uus vvs.
      Proof.
        intros; repeat let_pair_simpl; split.
        - intros H. pose proof relfs_split us vs.
          repeat let_pair_simpl; auto.
        - intros [Hx Huv]. pose proof combine_relfs _ _ _ _ Hx Huv.
          unravel in *. pose proof split_combine us.
          pose proof split_combine vs. repeat let_pair_simpl; auto.
      Qed.

      Lemma relfs_split_map_iff : forall us vs,
          relfs us vs <->
          Forall2 keq (List.map fst us) (List.map fst vs) /\
          Forall2 R (List.map snd us) (List.map snd vs).
      Proof.
        intros. pose proof relfs_split_iff us vs. repeat let_pair_simpl.
        rewrite split_map in Heqp. rewrite split_map in Heqp0.
        repeat let_pair_simpl. assumption.
      Qed.

      Context `{EqDec K keq}.

      Lemma relfs_get_l : forall k u us vs,
          relfs us vs ->
          get k us = Some u -> exists v : V, get k vs = Some v /\ R u v.
      Proof.
        intros x u us vs HRs.
        generalize dependent x; generalize dependent u.
        induction HRs; intros u z Hu;
        unravel in *; try discriminate.
        destruct x as [xu u']; destruct y as [xv v']; inv H0; unravel in *.
        destruct (equiv_dec z xu) as [Hzu | Hzu];
          destruct (equiv_dec z xv) as [Hzv | Hzv];
          unfold equiv, complement in *; eauto.
        - inv Hu. exists v'; auto.
        - assert (equiv z xv) by (etransitivity; eauto).
          contradiction.
        - symmetry in Hzv.
          assert (keq xu z) by (etransitivity; eauto).
          symmetry in H0; contradiction.
      Qed.

      Lemma relfs_get_r : forall k (v : V) us vs,
        relfs us vs ->
        get k vs = Some v -> exists u : U, get k us = Some u /\ R u v.
      Proof.
      intros x v us vs HRs.
      generalize dependent x;
        generalize dependent v.
      induction HRs; intros v z Hu;
        unravel in *; try discriminate;
      destruct x as [xu u']; destruct y as [xv v']; inv H0; unravel in *.
      destruct (equiv_dec z xu) as [Hzu | Hzu];
        destruct (equiv_dec z xv) as [Hzv | Hzv];
        unfold equiv, complement in *; eauto.
      - inv Hu. exists u'; auto.
      - assert (equiv z xv) by (etransitivity; eauto).
        contradiction.
      - symmetry in H1.
        assert (equiv z xu) by (etransitivity; eauto).
        contradiction.
      Qed.

      Lemma get_relfs : forall k (u : U) (v : V) us vs,
          get k us = Some u -> get k vs = Some v ->
          relfs us vs -> R u v.
      Proof.
      intros x u v us vs Hu Hv HRs.
      generalize dependent x;
        generalize dependent v;
        generalize dependent u.
      induction HRs; intros u v z Hu Hv;
        unravel in *; try discriminate.
      destruct x as [xu u']; destruct y as [xv v']; unravel in *.
      inv H0; unravel in *.
      destruct (equiv_dec z xu) as [Hzu | Hzu];
        destruct (equiv_dec z xv) as [Hzv | Hzv];
        unfold equiv, complement in *; eauto.
      - inv Hu; inv Hv; auto.
      - assert (equiv z xv) by (etransitivity; eauto).
        contradiction.
      - symmetry in H1.
        assert (equiv z xu) by (etransitivity; eauto).
        contradiction.
      Qed.
    End FieldRelations.

    (** Decidable Equality *)
    Section DecEq.
      Context {K U : Type}.
      Context {keq : K -> K -> Prop}.
      Context `{Equivalence K keq}.
      Context `{EqDec K keq}.
      Variable feq : U -> U -> bool.

      Definition eqb_f : f K U -> f K U -> bool :=
        fun '(x1, u1) '(x2, u2) => equiv_dec x1 x2 &&&& feq u1 u2.
      (**[]*)

      Fixpoint eqb_fs (fs1 fs2 : fs K U) : bool :=
        match fs1, fs2 with
        | [], _::_ | _::_, [] => false
        | [], [] => true
        | f1::fs1, f2::fs2 => eqb_f f1 f2 && eqb_fs fs1 fs2
        end.
      (**[]*)

      Section ReflxEqb.
        Hypothesis Hfeq : forall u : U, feq u u = true.

        Lemma eqb_f_reflx : forall fld : f K U, eqb_f fld fld = true.
        Proof.
          Hint Rewrite Hfeq.
          intros [k u]; unravel; equiv_dec_refl_tactic;
          autorewrite with core; auto.
          assert (keq k k) by reflexivity; contradiction.
        Qed.

        Lemma eqb_fs_reflx : forall flds : fs K U, eqb_fs flds flds = true.
        Proof.
          Hint Rewrite eqb_f_reflx.
          induction flds; unravel; autorewrite with core; auto.
        Qed.
      End ReflxEqb.
    End DecEq.
  End FieldLibrary.

  Module RelfEquiv.
    Instance RelfEquiv
             (K U : Type)
             (keq : K -> K -> Prop) `{Equivalence K keq}
             (R : U -> U -> Prop) `{Equivalence U R}
      : Equivalence (@relf _ _ _ keq _ R) :=
      ProdEquiv keq R.
    (**[]*)

    Instance RelfsEquiv
             (K U : Type)
             (keq : K -> K -> Prop) `{Equivalence K keq}
             (R : U -> U -> Prop) `{Equivalence U R}
      : Equivalence (@relfs _ _ _ keq _ R) :=
      Forall2Equiv (relf R).
    (**[]*)

    Section EqReflect.
      Context {K U : Type}.
      Context {keq : K -> K -> Prop}.
      Context `{EQkeq : Equivalence K keq}.
      Context `{EQDeckeq : EqDec K keq}.
      Variable R : U -> U -> Prop.
      Context `{EQR : Equivalence U R}.
      Variable feq : U -> U -> bool.
      Hypothesis HR : forall u1 u2, reflect (R u1 u2) (feq u1 u2).

      Lemma equiv_eqb_f : forall (f1 f2 : f K U),
          equiv f1 f2 -> eqb_f feq f1 f2 = true.
      Proof.
        unfold equiv in *; intros [? ?] [? ?] [? ?]; unravel in *;
        match goal with
        | Hx : keq ?x1 ?x2,
          HRu: R ?u1 ?u2 |- _
          => specialize HR with u1 u2; inv HR;
              destruct (equiv_dec x1 x2) as [? | ?];
              unfold equiv, complement in *; auto
        end.
      Qed.

      Lemma equiv_eqb_fs : forall (fs1 fs2 : fs K U),
          equiv fs1 fs2 -> eqb_fs feq fs1 fs2 = true.
      Proof.
        unfold equiv; intros ? ? ?;
        match goal with
        | H: relfs _ _ _ |- _ => induction H
        end; unravel; auto;
        match goal with
        | |- _ && _ = true => apply andb_true_intro; split;
                            try apply equiv_eqb_f; auto
        end.
      Qed.

      Lemma eqb_f_equiv : forall (f1 f2 : f K U),
          eqb_f feq f1 f2 = true -> equiv f1 f2.
      Proof.
        unfold equiv, relf; intros [? ?] [? ?] ?; unravel in *;
        match goal with
        | H: ?x &&&& feq ?u1 ?u2 = true |- _
          => specialize HR with u1 u2;
            destruct x as [? | ?]; inv HR;
              destruct (feq u1 u2) eqn:?;
            unfold equiv, complement in *; split; auto;
                try discriminate
        end.
      Qed.

      Lemma eqb_fs_equiv : forall (fs1 fs2 : fs K U),
          eqb_fs feq fs1 fs2 = true -> equiv fs1 fs2.
      Proof.
        unfold equiv; induction fs1 as [| ? ? ?]; intros [| ? ?] ?;
        unravel in *; try discriminate; constructor;
        unfold relfs in *;
        match goal with
        | H: _ && _ = true |- _ => apply andb_true_iff in H as [? ?]
        end; try apply eqb_f_equiv; eauto.
      Qed.
    End EqReflect.

    (** Syntactic Equality. *)
    Section RelfEq.
      Context {K V : Type}.

      Lemma eq_relf : forall f1 f2 : f K V, relf eq f1 f2 -> f1 = f2.
      Proof.
        intros [? ?] [? ?] [? ?]; unfold equiv in *;
        unravel in *; subst; reflexivity.
      Qed.

      Lemma eq_relfs : forall fs1 fs2 : fs K V, relfs eq fs1 fs2 -> fs1 = fs2.
      Proof.
        Hint Resolve eq_relf : core.
        intros ? ? H; induction H; auto; subst; f_equal; auto.
      Qed.
    End RelfEq.
  End RelfEquiv.

  Module FieldTactics.
    Ltac predf_destruct :=
      match goal with
      | H: predf_data _ (_, _) |- _ => unfold predf_data in H; unravel in *
      | H: predf_data _ ?f
        |- _ => destruct f as [? ?]; unfold predf_data in H; unravel in *
      end.
    (**[]*)

    Ltac invert_cons_predfs :=
      match goal with
      | H:predfs_data _ (_::_) |- _ => inv H; try predf_destruct
      end.
    (**[]*)

    Ltac ind_list_predfs :=
      match goal with
      | H: predfs_data _ ?fs
        |- _ => induction fs; try invert_cons_predfs
      end.
    (**[]*)

    Ltac ind_predfs_data :=
      match goal with
      | H: predfs_data _ _
        |- _ => induction H; try predf_destruct
      end.
    (**[]*)

    Ltac invert_nil_cons_relate :=
      match goal with
      | H:relfs _ [] (_::_) |- _ => inv H
      | H:relfs _ (_::_) [] |- _ => inv H
      end.
    (**[]*)

    Ltac relf_destruct :=
      match goal with
      | H:relf _ (_,_) (_,_) |- _ => destruct H as [? ?]; unravel in *
      | H:relf _ ?fu (_,_)
        |- _ => destruct fu as [? ?];
              destruct H as [? ?]; unravel in *
      | H:relf _ (_,_) ?fv
        |- _ => destruct fv as [? ?];
              destruct H as [? ?]; unravel in *
      | H:relf _ ?fu ?fv
        |- _ => destruct fu as [? ?];
              destruct fv as [? ?];
              destruct H as [? ?]; unravel in *
      end.
    (**[]*)

    Ltac invert_cons_cons_relate :=
      match goal with
      | H:relfs _ (_::_) (_::_) |- _ => inv H; try relf_destruct
      end.
    (**[]*)

    Ltac ind_list_relfs :=
      match goal with
      | H: relfs _ ?fs1 ?fs2
        |- _ => generalize dependent fs2;
              induction fs1; intros [| ? ?]; intros;
              try invert_nil_cons_relate;
              try invert_cons_cons_relate
      end.

    Ltac ind_relfs :=
      match goal with
      | H: relfs _ _ _
        |- _ => induction H; try relf_destruct
      end.
  End FieldTactics.
End Field.
