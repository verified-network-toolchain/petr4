Require Export Poulet4.AList Poulet4.ForallMap Coq.Classes.EquivDec.

Section Util.
  Variables
    (K U W : Type)
    (R: Relation_Definitions.relation K)
    (P : U -> W -> Prop).
  Context `{Equivalence K R}.
  
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
End Util.

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
