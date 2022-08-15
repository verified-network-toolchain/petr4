Require Export Poulet4.Utils.AList Poulet4.Utils.ForallMap Coq.Classes.EquivDec.

Section Util.
  Context {K V: Type}
          {R : Relation_Definitions.relation K}
          `{HKR: EqDec K R}.
  
  Lemma get_equiv : forall (kvs : list (K * V)) k₁ k₂,
      k₁ === k₂ -> get kvs k₁ = get kvs k₂.
  Proof.
    induction kvs as [| [k v] kvs IHkvs];
      intros k1 k2 Hk; cbn in *; try reflexivity.
    destruct (equiv_dec k1 k) as [Hk1k | Hk1k].
    - rewrite get_eq_cons by assumption.
      rewrite get_eq_cons; try reflexivity.
      symmetry in Hk; transitivity k1; assumption.
    - rewrite get_neq_cons by assumption.
      rewrite get_neq_cons; auto.
      intros H; apply Hk1k.
      transitivity k2; assumption.
  Qed.

  Lemma get_none_not_in_fst : forall (l : list (K * V)) (k : K),
      get l k = None -> forall k', k === k' -> ~ In k' (map fst l).
  Proof.
    intros l k Hnone k' Hk'k Hk'.
    apply in_fst_get_some in Hk' as [v Hv].
    erewrite get_equiv in Hnone by eassumption.
    rewrite Hnone in Hv; discriminate.
  Qed.

  Lemma not_in_fst_get_none : forall (l : list (K * V)) k,
      (forall k', k === k'  -> ~ In k' (map fst l)) -> get l k = None.
  Proof.
    intros l k H.
    destruct (get l k) as [v |] eqn:Hv; try reflexivity.
    apply get_some_in_fst in Hv as (k' & Hkk' & Hk').
    firstorder.
  Qed.

  Lemma AList_get_some_split : forall l (x : K) (v : V),
      AList.get l x = Some v -> exists k l₁ l₂,
        x === k /\ l = l₁ ++ (k, v) :: l₂ /\ AList.get l₁ x = None.
  Proof.
    intro l; induction l as [| [k a] l ihl]; intros x v h;
      cbn in *; try discriminate.
    destruct (equiv_dec x k) as [hxk | hxk].
    - rewrite get_eq_cons in h by assumption.
      injection h as h; subst.
      exists k, [], l; cbn. repeat split; auto.
    - rewrite get_neq_cons in h by assumption.
      apply ihl in h as (y & l1 & l2 & hxy & hl & hy); subst.
      exists y, ((k, a) :: l1), l2.
      rewrite get_neq_cons by assumption.
      repeat split; auto.
  Qed.
  
  Lemma AList_set_some_split : forall l l' (x : K) (v' : V),
      AList.set l x v' = Some l' -> exists k v l₁ l₂,
        x === k /\ l = l₁ ++ (k, v) :: l₂ /\ l' = l₁ ++ (x, v') :: l₂ /\ AList.get l₁ x = None.
  Proof.
    intro l; induction l as [| [y a] l ihl];
      intros [| [z b] l'] x v' h; cbn in *; try discriminate.
    - destruct (HKR x y) as [hxy | hxy].
      + inversion h.
      + destruct (set l x v'); inversion h.
    - destruct (HKR x y) as [hxy | hxy].
      + inversion h; subst.
        exists y, a, [], l'; cbn. repeat split; auto.
      + destruct (set l x v') as [kvs |] eqn:hkvs;
          cbn in *; inversion h; subst.
        pose proof ihl _ _ _ hkvs as (c & v & l1 & l2 & hxc & hl & hl' & hl1); subst.
        exists c, v, ((z, b) :: l1), l2; cbn.
        rewrite get_neq_cons by assumption.
        repeat split; auto.
  Qed.

  (*Lemma set_some_get : forall l l' (k : K) (v : V),
      set l k v = Some l' -> exists a, get l k = a.*)

  (** Removes the first equal key. *)
  Fixpoint remove_first (key : K) (l : list (K * V)) : list (K * V) :=
    match l with
    | [] => []
    | (k, v) :: l => if HKR key k then l else (k, v) :: remove_first key l
    end.

  Lemma remove_first_cons_equiv : forall key k v l,
      key === k -> remove_first key ((k, v) :: l) = l.
  Proof.
    intros key k v l hk; cbn.
    destruct (HKR key k) as [h | h]; try reflexivity.
    unfold "=/=" in h. contradiction.
  Qed.

  Lemma remove_first_sublist: forall key l, sublist (remove_first key l) l.
  Proof.
    intros. induction l; simpl.
    - exists []. simpl. auto.
    - destruct a as [k v]; destruct (HKR key k).
      + exists [(k, v)]. change ((k, v) :: l) with ([(k, v)] ++ l).
        apply Permutation.Permutation_app_comm.
      + destruct IHl as [l' ?]. exists l'. constructor. apply H.
  Qed.

End Util.

Section ALL.
  Variables
    (K U W : Type)
    (R: Relation_Definitions.relation K).
  Context `{HKR: EqDec K R}.

  Lemma key_unique_combine : forall (kvs : list (K * U)) (vs : list W),
      length kvs = length vs ->
      AList.key_unique (combine (map fst kvs) vs) = AList.key_unique kvs.
  Proof.
    intro kvs; induction kvs as [| [k v] kvs IHkvs];
      intros [| v' vs] Hlen; cbn in *;
        try (discriminate || reflexivity).
    destruct (get (combine (map fst kvs) vs) k)
      as [v'' |] eqn:Hv''.
    - apply get_some_in_fst in Hv'' as (k' & Hkk' & Hk').
      rewrite map_fst_combine in Hk' by (rewrite map_length; lia).
      apply in_fst_get_some in Hk' as [v''' Hv'''].
      erewrite get_equiv by eauto.
      rewrite Hv'''; reflexivity.
    - pose proof get_none_not_in_fst _ _ Hv'' as H.
      rewrite map_fst_combine in H by (rewrite map_length; lia).
      apply not_in_fst_get_none in H.
      rewrite H; apply IHkvs; lia.
  Qed.

  Variable P : U -> W -> Prop.

  Lemma Forall2_all_values : forall us ws ks,
      length ks = length us -> length ks = length ws ->
      Forall2 P us ws <->
      all_values P (combine ks us) (combine ks ws).
  Proof.
    intros us ws ks Hlku Hlkw; unfold all_values.
    rewrite Forall2_conj.
    rewrite Forall2_map_both with (f := fst) (g := fst).
    rewrite Forall2_map_both with (f := snd) (g := snd).
    repeat rewrite map_snd_combine by auto.
    repeat rewrite map_fst_combine by auto.
    rewrite Forall2_Forall, Forall_forall.
    intuition.
  Qed.

  Lemma all_values_keys_eq : forall us ws,
      all_values P us ws -> map fst us = map fst ws.
  Proof.
    intros us ws HPuws.
    unfold all_values in HPuws.
    rewrite Forall2_conj in HPuws.
    destruct HPuws as [HPl _].
    rewrite Forall2_map_both in HPl.
    rewrite Forall2_eq in HPl.
    assumption.
  Qed.

  Lemma all_values_remove_first: forall key us ws,
      all_values P us ws -> all_values P (remove_first key us) (remove_first key ws).
  Proof.
    intros. induction H; simpl.
    - constructor.
    - destruct x as [k v1]. destruct y as [k' v2]. destruct H. simpl in *. subst k'.
      destruct (HKR key k). 1: apply H0. constructor; try split; auto.
  Qed.

  Lemma all_values_app : forall us1 us2 ws1 ws2,
      length us1 = length ws1 ->
      all_values P (us1 ++ us2) (ws1 ++ ws2) ->
      all_values P us1 ws1 /\ all_values P us2 ws2.
  Proof.
    intros us1 us2 ws1 ws2 hlen h.
    unfold all_values in *.
    auto using Forall2_length_eq_app.
  Qed.
End ALL.

Section Rel.
  Context {K A B : Type} {R: Relation_Definitions.relation K}
          `{H: Equivalence K R} {KEqDec: EqDec K R}.

  Lemma map_fst_get : forall (kas : list (K * A)) (kbs : list (K * B)),
      map fst kas = map fst kbs ->
      forall k, (get kas k = None -> get kbs k = None) /\
           forall a, get kas k = Some a -> exists b, get kbs k = Some b.
  Proof.
    unfold get.
    intro kas; induction kas as [| [k a] kas IHkas];
      intros [| [k' b] kbs] Heq; cbn in *; try discriminate.
    - firstorder discriminate.
    - injection Heq as Hk Hkas; subst; intro k.
      apply IHkas with (k:=k) in Hkas; clear IHkas.
      destruct Hkas as [Hnone Hsome];
        destruct (KEqDec k k') as [Hkk' | Hkk']; split; eauto; try discriminate.
  Qed.

  Lemma map_fst_key_unique : forall (kas : list (K * A)) (kbs : list (K * B)),
      map fst kas = map fst kbs ->
      key_unique kas = key_unique kbs.
  Proof.
    intro kas; induction kas as [| [k a] kas IHkas];
      intros [| [k' b] kbs] Heq; cbn in *; try discriminate || reflexivity.
    injection Heq as Hk Hkas; subst.
    apply IHkas in Hkas as IH; clear IHkas.
    apply map_fst_get with (k:=k') in Hkas as [Hnone Hsome].
    destruct (get kas k') as [a' |] eqn:Hget.
    - assert (Hb: exists b, get kbs k' = Some b) by eauto.
      destruct Hb as [b' Hb]; rewrite Hb; reflexivity.
    - rewrite Hnone by reflexivity; assumption.
  Qed.

  Section Map.
    Variable (f : A -> B).

    Definition map_values  : AList K A R -> AList K B R :=
      List.map (fun '(k,a) => (k,f a)).

    Lemma get_map_values : forall (l : AList K A R) (k : K),
        get (map_values l) k = option_map f (get l k).
    Proof.
      unfold get.
      induction l as [| [ky a] l IHl]; intros k; simpl; auto.
      destruct (KEqDec k ky) as [Hkky | Hkky];
        unfold equiv, complement in *; simpl in *; auto.
    Qed.

    Lemma key_unique_map_values : forall (l : AList K A R),
        key_unique (map_values l) = key_unique l.
    Proof.
      intro l; induction l as [| [k a] l IHl]; cbn in *; auto.
      destruct (get (map_values l) k) as [b |] eqn:Hget;
        rewrite get_map_values in Hget;
        destruct (get l k) as [a' |]; cbn in *;
          try discriminate; auto.
    Qed.
  End Map.

  Section Relate.
    Variable Q : A -> B -> Prop.

    Lemma get_relate_values : forall al bl k (a : A) (b : B),
        all_values Q al bl ->
        get al k = Some a ->
        get bl k = Some b ->
        Q a b.
    Proof.
      unfold get, all_values.
      intro al; induction al as [| [ka a'] al IHal];
        intros [| [kb b'] bl] k a b Hall Hgetal Hgetbl; cbn in *;
          inversion Hall; subst; try discriminate.
      destruct (KEqDec k ka) as [Hka | Hka];
        destruct (KEqDec k kb) as [Hkb | Hkb];
        unfold equiv, complement in *; simpl in *; subst;
          repeat match goal with
                 | H: Some _ = Some _
                   |- _ => inversion H; subst; clear H
                 end;
          match goal with
          | H: _ /\ _ |- _ => destruct H; subst; eauto; try contradiction
          end.
    Qed.

    Lemma all_values_key_unique : forall (kas : list (K * A)) (kbs : list (K * B)),
        all_values Q kas kbs ->
        key_unique kas = key_unique kbs.
    Proof.
      intros kas kbs h.
      unfold all_values in h.
      rewrite Forall2_conj in h.
      destruct h as [h _].
      rewrite Forall2_map_both,Forall2_eq in h.
      auto using map_fst_key_unique.
    Qed.
    
    Lemma key_unique_all_values_split :
      forall kas1 kas2 kbs1 kbs2 (ka kb : K) (a : A) (b : B),
        ka === kb ->
        key_unique (kas1 ++ (ka, a) :: kas2) = true ->
        key_unique (kbs1 ++ (kb, b) :: kbs2) = true ->
        all_values Q (kas1 ++ (ka, a) :: kas2) (kbs1 ++ (kb, b) :: kbs2) ->
        ka = kb /\ Q a b /\ all_values Q kas1 kbs1 /\ all_values Q kas2 kbs2.
    Proof.
      unfold all_values.
      intros kas1; induction kas1 as [| [ka1 a1] kas1 ih];
        intros kas2 [| [kb1 b1] kbs1] kbs2 ka kb a b hkakb huniqa huniqb h;
        cbn in *; inversion h; clear h; subst; cbn in *.
      - destruct H3 as [? hq]; subst.
        repeat split; auto.
      - destruct H3 as [? hq]; subst.
        destruct (get (kbs1 ++ (kb, b) :: kbs2) kb1) as [b1' |] eqn:hgetbs;
          cbn in *; try discriminate.
        destruct (get kas2 kb1) as [a1' |] eqn:hgetas;
          cbn in *; try discriminate.
        rewrite (get_equiv _ _ _ hkakb) in hgetas.
        apply all_values_keys_eq with (R:=R) in H5; auto.
        assert (hin: In kb (map fst (kbs1 ++ (kb, b) :: kbs2))).
        { rewrite map_app; cbn. apply in_elt. }
        rewrite <- H5 in hin.
        pose proof get_none_not_in_fst _ _ hgetas kb ltac:(intuition) as h.
        contradiction.
      - destruct H3 as [? hq]; subst.
        destruct (get (kas1 ++ (ka, a) :: kas2) kb) as [a1' |] eqn:hgetas;
          cbn in *; try discriminate.
        destruct (get kbs2 kb) as [b1' |] eqn:hgetbs;
          cbn in *; try discriminate.
        symmetry in hkakb.
        rewrite (get_equiv _ _ _ hkakb) in hgetbs.
        apply all_values_keys_eq with (R:=R) in H5; auto.
        assert (hin: In ka (map fst (kas1 ++ (ka, a) :: kas2))).
        { rewrite map_app; cbn. apply in_elt. }
        rewrite H5 in hin.
        pose proof get_none_not_in_fst _ _ hgetbs ka ltac:(intuition) as h.
        contradiction.
      - destruct H3 as [? hq]; subst.
        destruct (get (kas1 ++ (ka, a) :: kas2) kb1) as [a' |] eqn:hgetas;
          cbn in *; try discriminate.
        destruct (get (kbs1 ++ (kb, b) :: kbs2) kb1) as [b' |] eqn:hgetbs;
          cbn in *; try discriminate.
        pose proof ih _ _ _ _ _ _ _ hkakb huniqa huniqb H5 as IH; clear ih.
        destruct IH as (hkab & hqab & h1 & h2).
        repeat split; auto.
    Qed.
  End Relate.
End Rel.
