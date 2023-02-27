Require Import Poulet4.Utils.Util.Utiliser
        Coq.Logic.FunctionalExtensionality.

(** * Environments *)
Module Clmt.

  (** Definition of environments.
      NOTE: Must be a partial map!
      Please do not change! *)
  Definition t (D T : Set) : Set := D -> option T.

  (** The empty environment. *)
  Definition empty (D T : Set) : t D T := fun _ => None.

  Section EnvDefs.
    Context {D T : Set}.
    
    Context {HE : EqDec D eq}.

    (** Updating the environment. *)
    Definition bind (x : D) (v : T) (e : t D T) : t D T :=
      fun y => if x == y then Some v else e y.
    (**[]*)

    Definition remove (d : D) (e : t D T) : t D T :=
      fun y => if d == y then None else e y.

    (** Gather values given a list of keys. *)
    Definition gather (e: t D T) : list D -> list T :=
      List.fold_right
        (fun k acc =>
           match e k with
           | Some v => v :: acc
           | None => acc
           end) [].
    
    (** Scope Shadowing, [e1] shadows [e2]. *)
    Definition shadow (e1 e2 : t D T) : t D T :=
      fun d => match e1 d, e2 d with
            | Some _, Some v
            | Some v, None => Some v
            | _     , _    => None
            end.
    (**[]*)
    
    Definition sub_env (e1 e2 : t D T) : Prop :=
      forall k v, e1 k = Some v -> e2 k = Some v.
    
    Definition disjoint (e₁ e₂ : t D T) : Prop := forall k,
        (e₁ k <> None -> e₂ k = None) /\
        (e₂ k <> None -> e₁ k = None).
    
    Definition union (e₁ e₂ : t D T) : t D T :=
      fun y => match e₁ y with
            | Some v => Some v
            | None   => e₂ y
            end.

    Definition strip (e₁ e₂ : t D T) : t D T :=
      fun y => match e₁ y with
            | Some _ => None
            | None   => e₂ y
            end.
    
    Definition disjoint_union (e₁ e₂ e₃ : t D T) : Prop :=
      disjoint e₁ e₂ /\ union e₁ e₂ = e₃.
    
    Section Lemmas.
      Local Hint Extern 0 => simpl_equiv_dec : core.
      Local Hint Extern 0 => simpl_equiv_dec_hyp : core.
      Local Hint Unfold bind : core.
      
      Lemma bind_sound : forall x v e,
          bind x v e x = Some v.
      Proof.
        intros; simpl; autounfold with *; auto.
      Qed.
      
      Lemma bind_complete : forall x y v e,
          y <> x -> bind y v e x = e x.
      Proof.
        intros; simpl; autounfold with *; auto.
      Qed.
      
      Lemma bind_twice : forall x y v v' e,
          bind x v (bind x v' e) y = bind x v e y.
      Proof.
        intros; simpl; autounfold with *; destruct_if; auto.
      Qed.
      
      Lemma bind_diff_comm : forall x y z u v e,
          x <> y ->
          bind x u (bind y v e) z = bind y v (bind x u e) z.
      Proof.
        intros; simpl; autounfold with *;
          repeat (destruct_if; auto); subst; contradiction.
      Qed.
    
      Global Instance sub_env_reflexive : Reflexive sub_env.
      Proof. firstorder. Qed.

      Global Instance sub_env_transitive : Transitive sub_env.
      Proof. firstorder. Qed.

      Global Instance sub_env_antisymmetric
        : @Antisymmetric _ eq _ sub_env.
      Proof.
        unfold Antisymmetric, sub_env.
        intros e1 e2 H1 H2.
        extensionality k.
        destruct (e2 k) as [v2 |] eqn:He2; auto.
        destruct (e1 k) as [v1 |] eqn:He1; auto.
        apply H1 in He1; rewrite He2 in He1; discriminate.
      Qed.

      (** TODO: [e ⊆ bind k v e <-> find k e = None \/ find k e = Some v] *)
      Lemma find_none_bind_sub_env : forall e k v,
          e k = None -> sub_env e (bind k v e).
      Proof.
        unfold sub_env, bind;
          intros e k v H k' v' Hkv'; simpl.
        destruct_if; auto; subst.
        rewrite H in Hkv'; discriminate.
      Qed.
      
      Lemma union_sub_env :
        forall e1 e2, sub_env e1 (union e1 e2).
      Proof.
        unfold sub_env, union;
          intros e1 e2 k v Hkv.
        rewrite Hkv; reflexivity.
      Qed.
      
      Lemma disjoint_sym : forall e1 e2,
          disjoint e1 e2 -> disjoint e2 e1.
      Proof.
        firstorder.
      Qed.
      
      Lemma forall_conj_distr : forall (U : Set) (P Q : U -> Prop),
          (forall u, P u /\ Q u) <-> (forall u, P u) /\ forall u, Q u.
      Proof.
        firstorder.
      Qed.
      
      Lemma disjoint_nexists : forall e1 e2,
          disjoint e1 e2 ->
          ~ exists k v, e1 k = Some v /\ e2 k = Some v.
      Proof.
        intros e1 e2 H (k & v & He1 & He2).
        unfold disjoint in H; specialize H with k.
        destruct H as [H1 H2].
        assert (Hnone: e1 k <> None).
        { rewrite He1; discriminate. }
        apply H1 in Hnone. rewrite Hnone in He2.
        discriminate.
      Qed.
      
      (** Need assumption that [e1]
          and [e2] are not empty. *)
      Lemma disjoint_eq_env : forall e1 e2,
          disjoint e1 e2 -> e1 <> e2.
      Proof.
        unfold disjoint; intros e1 e2 Hd H; subst.
        apply forall_conj_distr in Hd.
        destruct Hd as [H1 _].
      Abort.
            
      Lemma find_union_l : forall e1 e2 k v,
          e1 k = Some v ->
          union e1 e2 k = Some v.
      Proof.
        intros e1 e2 k v H; unfold union;
          rewrite H; reflexivity.
      Qed.
      
      Local Hint Resolve find_union_l : core.
      
      Lemma find_union_r : forall e1 e2 k,
          e1 k = None ->
          union e1 e2 k = e2 k.
      Proof.
        unfold union; intros e1 e2 k H; rewrite H; reflexivity.
      Qed.

      Local Hint Resolve find_union_r : core.
      
      Lemma find_union_some : forall e1 e2 k v,
          union e1 e2 k = Some v ->
          e1 k = Some v \/ e2 k = Some v.
      Proof.
        intros e1 e2 k v H; unfold union in *.
        destruct (e1 k) as [v1 |] eqn:Hke1; auto.
      Qed.

      Local Hint Resolve find_union_some : core.
      
      Lemma disjoint_union_eq_env : forall e1 e2,
          disjoint e1 e2 -> union e1 e2 = union e2 e1.
      Proof.
        unfold disjoint; intros e1 e2 H.
        extensionality k.
        unfold disjoint. apply forall_conj_distr in H as [H1 H2].
        specialize H1 with k; specialize H2 with k.
        unfold union.
        destruct (e1 k) as [v1 |] eqn:He1;
          destruct (e2 k) as [v2 |] eqn:He2; auto;
            assert (Hneq: Some v1 <> None) by discriminate;
            apply H1 in Hneq; discriminate.
      Qed.
      
      Lemma disjoint_empty : forall e, disjoint e (empty D T).
      Proof.
        unfold disjoint; intros e k; split;
          unravel; auto; try contradiction.
      Qed.
      
      Local Hint Resolve disjoint_union_eq_env : core.
      Local Hint Resolve disjoint_sym : core.
      
      Lemma disjoint_union_sym : forall e1 e2 e3,
          disjoint_union e1 e2 e3 -> disjoint_union e2 e1 e3.
      Proof.
        unfold disjoint_union.
        intros e1 e2 e3 [Hd Heq]; split; subst; auto.
      Qed.
      
      Lemma disjoint_sub_env_union_inj_r : forall l r r',
          disjoint l r ->
          sub_env (union l r) (union l r') -> sub_env r r'.
      Proof.
        unfold disjoint, sub_env; intros l r r' Hd Hs k v Hkv;
          specialize Hd with k; specialize Hs with k v;
            destruct Hd as [Hd1 Hd2].
        assert (Hnone: r k <> None) by (rewrite Hkv; discriminate).
        apply Hd2 in Hnone.
        assert (union l r k = Some v) by (rewrite <- Hkv; auto).
        apply Hs in H. apply find_union_some in H.
        destruct H as [H | H];
          try rewrite H in Hnone; auto; discriminate.
      Qed.
      
      Lemma eq_env_union_inj : forall l r r',
          disjoint l r -> disjoint l r' ->
          union l r = union l r' -> r = r'.
      Proof.
        unfold disjoint; intros l r r' Hr Hr' Hu.
        extensionality k.
        specialize Hr with k; specialize Hr' with k.
        destruct Hr as [Hlr Hrl]; destruct Hr' as [Hlr' Hrl'].
        apply equal_f with k in Hu.
        unfold union in Hu.
        destruct (l k) as [v |] eqn:Hlk; auto.
        assert (Hneq: Some v <> None) by discriminate.
        pose proof Hlr Hneq as Hrk;
          pose proof Hlr' Hneq as Hrk';
          rewrite Hrk, Hrk'; reflexivity.
      Qed.
      
      Local Hint Resolve eq_env_union_inj : core.
      
      Lemma disjoint_union_unique_eq_env_r : forall l r r' e,
          disjoint_union l r e ->
          disjoint_union l r' e -> r = r'.
      Proof.
        unfold disjoint_union.
        intros l r r' e [Hdr Hr] [Hdr' Hr']; subst.
        eauto.
      Qed.
      
      Lemma disjoint_union_unique_eq_env :  forall l r e e',
          disjoint_union l r e ->
          disjoint_union l r e' -> e = e'.
      Proof.
        unfold disjoint_union;
          intros l r e e' [Hd He] [Hd' He'];
          subst; reflexivity.
      Qed.
      
      Lemma sub_env_union : forall e1 e2 e3,
          sub_env (union e1 e2) e3 -> sub_env e1 e3.
      Proof.
        unfold sub_env; intros e1 e2 e3 H k v Hkv; eauto.
      Qed.

      Local Hint Resolve sub_env_union : core.
      Local Hint Resolve union_sub_env : core.
      
      Lemma disjoint_union_sub_env : forall e1 e2 e3,
          disjoint_union e1 e2 e3 -> sub_env e1 e3.
      Proof.
        intros e1 e2 e3 [Hd He3]; subst; auto.
      Qed.
      
      Local Hint Resolve disjoint_empty : core.
      Local Hint Resolve disjoint_sym : core.
    
      Lemma sub_env_disjoint_union_exists : forall e1 e2,
          sub_env e1 e2 -> exists e, disjoint_union e1 e e2.
      Proof.
        intros e1 e2 Hs.
        unfold disjoint_union.
        exists (strip e1 e2).
        (* TODO: helper lemmas. *)
      Admitted.
    End Lemmas.
  End EnvDefs.

  Section MapVals.
    Context {D U V : Set}.
    Variable (f : U -> V).
  
    Definition map_vals (e : t D U) : t D V :=
      fun k => e k >>| f.
  End MapVals.

  Module Notations.
    Declare Scope climate_scope.
    Delimit Scope climate_scope with climate.
    
    Notation "e1 '⊆' e2"
      := (sub_env e1 e2)
           (at level 80, no associativity) : type_scope.
    Notation "'∅'"
      := (empty _ _) (at level 0, no associativity) : climate_scope.
    Notation "x ↦ v ',,' e"
      := (bind x v e)
           (at level 41, right associativity) : climate_scope.
    Notation "e1 ≪ e2"
      := (shadow e1 e2)
           (at level 41, right associativity) : climate_scope.
  End Notations.
End Clmt.
