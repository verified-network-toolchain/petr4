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
  End Relate.
End Rel.
