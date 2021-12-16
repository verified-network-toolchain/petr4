Require Import Poulet4.Utils.Util.Utiliser.

Declare Custom Entry p4env.

(** * Environments *)
Module Clmt.

  (** Definition of environments.
      NOTE: Must be a partial map!
      Please do not change! *)
  Definition t (D T : Type) : Type := D -> option T.

  (** The empty environment. *)
  Definition empty (D T : Type) : t D T := fun _ => None.

  Section EnvDefs.
    Context {D T : Type}.
    
    Context {HE : EqDec D eq}.

    (** Updating the environment. *)
    Definition bind (x : D) (v : T) (e : t D T) : t D T :=
      fun y => if x == y then Some v else e y.
    (**[]*)

    Definition remove (d : D) (e : t D T) : t D T :=
      fun y => if d == y then None else e y.
  
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
      fun y => match e₁ y, e₂ y with
            | Some v, _ | _, Some v => Some v
            | _, _ => None
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
        unfold Antisymmetric.
      Admitted.

      (** TODO: [e ⊆ bind k v e <-> find k e = None \/ find k e = Some v] *)
      Lemma find_none_bind_sub_env : forall e k v,
          find k e = None -> sub_env e (bind k v e).
      Proof.
        unfold sub_env, bind;
          intros e k v H k' v' Hkv'; simpl.
        destruct_if; auto.
        assert (Hfind: find k' e = find k e)
          by auto using find_equiv_rel.
        rewrite Hfind, H in Hkv'; discriminate.
      Qed.
      
      Lemma bind_sub_env_find_none : forall e k v,
          sub_env e (bind k v e) ->
          find k e = None \/ find k e = Some v.
      Proof.
        unfold sub_env, bind;
          intro e; induction e as [| [d t] e IHe]; simpl in *;
            intros ky vl H; auto.
      Abort.
      
      Lemma scope_shadow_sub_env :
        forall e1 e2, sub_env e1 (scope_shadow e1 e2).
      Proof.
        unfold sub_env, scope_shadow;
          intros e1 e2 k v Hkv.
        induction e1 as [| [k1 v1] e1 IHe1];
          simpl in *; auto; try discriminate.
      Qed.
      
      Lemma disjoint_sym : forall e1 e2,
          disjoint e1 e2 -> disjoint e2 e1.
      Proof.
        firstorder.
      Qed.
      
      Lemma forall_conj_distr : forall (U : Type) (P Q : U -> Prop),
          (forall u, P u /\ Q u) <-> (forall u, P u) /\ forall u, Q u.
      Proof.
        firstorder.
      Qed.
      
      Lemma disjoint_nexists : forall e1 e2,
          disjoint e1 e2 -> ~ exists k v, find k e1 = Some v /\ find k e2 = Some v.
      Proof.
        intros e1 e2 H (k & v & He1 & He2).
        unfold disjoint in H; specialize H with k.
        destruct H as [H1 H2].
        assert (Hnone: find k e1 <> None).
        { rewrite He1; discriminate. }
        apply H1 in Hnone. rewrite Hnone in He2.
        discriminate.
      Qed.
      
      (** Need assumption that [e1]
          and [e2] are not empty. *)
      Lemma disjoint_eq_env : forall e1 e2,
          disjoint e1 e2 -> ~ eq_env e1 e2.
      Proof.
        unfold disjoint, eq_env, sub_env.
        intros e1 e2 Hd [Hs1 Hs2].
      Abort.
      
      Lemma find_app_eq : forall e1 e2 k,
          find k (e1 ++ e2) =
          match find k e1 with
          | Some v => Some v
          | None   => find k e2
          end.
      Proof.
        intros e1; induction e1 as [| [k1 v1] e1 IHe1];
          intros e2 k; unravel; auto.
        destruct_if; auto.
      Qed.
      
      Lemma find_app_l : forall e1 e2 k v,
          find k e1 = Some v ->
          find k (e1 ++ e2) = Some v.
      Proof.
        intros e1 e2 k v H; rewrite find_app_eq, H; reflexivity.
      Qed.
      
      Lemma find_app_r : forall e1 e2 k,
          find k e1 = None ->
          find k (e1 ++ e2) = find k e2.
      Proof.
        intros e1 e2 k H; rewrite find_app_eq, H; reflexivity.
      Qed.
      
      Lemma find_app_some : forall e1 e2 k v,
          find k (e1 ++ e2) = Some v ->
          find k e1 = Some v \/ find k e2 = Some v.
      Proof.
        intros e1 e2 k v H.
        rewrite find_app_eq in H.
        destruct (find k e1) as [v1 |] eqn:Hke1; auto.
      Qed.
      
      Lemma disjoint_append_eq_env : forall e1 e2,
          disjoint e1 e2 -> eq_env (e1 ++ e2) (e2 ++ e1).
      Proof.
        unfold disjoint, eq_env, sub_env;
          intros e1 e2 Hd; split; intros k v Hkv;
            rewrite find_app_eq in *;
            specialize Hd with k; destruct Hd as [Hd1 Hd2];
              destruct (find k e1) as [v1 |] eqn:He1;
              destruct (find k e2) as [v2 |] eqn:He2; auto;
                assert (Hneq: Some v1 <> None) by discriminate;
                apply Hd1 in Hneq; discriminate.
      Qed.
      
      Lemma disjoint_nil : forall e, disjoint e [].
      Proof.
        unfold disjoint; intros e k; split;
          unravel; auto; try contradiction.
      Qed.
      
      Local Hint Resolve disjoint_append_eq_env : core.
      Local Hint Resolve disjoint_sym : core.
      
      Lemma disjoint_union_sym : forall e1 e2 e3,
          disjoint_union e1 e2 e3 -> disjoint_union e2 e1 e3.
      Proof.
        unfold disjoint_union.
        intros e1 e2 e3 [Hd Heq]; split; auto.
        assert (eq_env (e1 ++ e2) (e2 ++ e1)) by auto.
        etransitivity; eauto.
      Qed.
      
      Lemma disjoint_sub_env_app_inj_r : forall l r r',
          disjoint l r ->
          sub_env (l ++ r) (l ++ r') -> sub_env r r'.
      Proof.
        unfold disjoint, sub_env; intros l r r' Hd Hs k v Hkv;
          specialize Hd with k; specialize Hs with k v;
            destruct Hd as [Hd1 Hd2].
        assert (Hnone: find k r <> None) by (rewrite Hkv; discriminate).
        apply Hd2 in Hnone.
        repeat rewrite find_app_eq, Hnone in Hs; auto.
      Qed.
      
      Lemma eq_env_disjoint : forall e1 e2 e3,
          eq_env e1 e2 -> disjoint e1 e3 -> disjoint e2 e3.
      Proof.
        unfold eq_env, sub_env, disjoint;
          intros e1 e2 e3 [Hs1 Hs2] Hd k;
          specialize Hs1 with (k := k); specialize Hs2 with (k := k);
            specialize Hd with k; destruct Hd as [Hd1 Hd2]; split; intros H.
        - apply Hd1.
          destruct (find k e2) as [v2 |] eqn:Hv2; try contradiction.
          assert (Hke1: find k e1 = Some v2) by auto.
          rewrite Hke1; discriminate.
        - apply Hd2 in H.
          destruct (find k e2) as [v2 |] eqn:Hv2; auto.
          assert (Hke1 : find k e1 = Some v2) by auto.
          rewrite Hke1 in H; discriminate.
      Qed.
      
      Local Hint Resolve disjoint_sub_env_app_inj_r : core.
      
      Lemma eq_env_app_inj : forall l r r',
          disjoint l r -> disjoint l r' ->
          eq_env (l ++ r) (l ++ r') -> eq_env r r'.
      Proof.
        unfold eq_env; intuition; eauto.
      Qed.
      
      Local Hint Resolve eq_env_app_inj : core.
      
      Lemma disjoint_union_unique_eq_env_r : forall l r r' e,
          disjoint_union l r e ->
          disjoint_union l r' e -> eq_env r r'.
      Proof.
        unfold disjoint_union.
        intros l r r' e [Hdr Hr] [Hdr' Hr'].
        assert (Hlrr': eq_env (l ++ r) (l ++ r')).
        { symmetry in Hr'; transitivity e; auto. }
        eauto.
      Qed.
      
      Lemma disjoint_union_unique_eq_env :  forall l r e e',
          disjoint_union l r e ->
          disjoint_union l r e' -> eq_env e e'.
      Proof.
        unfold disjoint_union; firstorder.
      Qed.
      
      Lemma app_sub_env : forall e1 e2 e3,
          sub_env (e1 ++ e2) e3 -> sub_env e1 e3.
      Proof.
        unfold sub_env; intros e1 e2 e3 H k v Hkv;
        specialize H with k v.
      rewrite find_app_eq, Hkv in H; auto.
    Qed.

    Local Hint Resolve app_sub_env : core.
    
    Lemma disjoint_union_sub_env : forall e1 e2 e3,
        disjoint_union e1 e2 e3 -> sub_env e1 e3.
    Proof.
      unfold disjoint_union, eq_env; intuition; eauto.
    Qed.

    Lemma sub_env_bind_l : forall l r k v,
        sub_env ((k,v) :: l) r <->
        find k r = Some v /\
        match find k l with
        | None    => sub_env l r
        | Some v' => (v = v' /\ sub_env l r) \/ False (* TODO? *)
        end.
    Abort.
    
    Local Hint Resolve disjoint_nil : core.
    Local Hint Resolve disjoint_sym : core.
    
    Lemma sub_env_bind_r : forall l r k v,
        sub_env l (bind k v r) ->
        sub_env l r \/ find k l = Some v.
    Proof.
      unfold sub_env, bind.
      intro l; induction l as [| [kl vl] l IHl];
        intros r k v Hs.
      - left; intros ks vs Hksvs; simpl in *; discriminate.
      - specialize IHl with r k v; unravel in *.
        destruct_if.
    Abort.
    
    Lemma sub_env_disjoint_union_exists : forall e1 e2,
        sub_env e1 e2 -> exists e, disjoint_union e1 e e2.
    Proof.
      intros e1 e2 Hs.
      unfold disjoint_union.
      induction e1 as [| [k1 v1] e1 IHe1].
      - firstorder.
      - (* need unique representation maybe
           for proof. *)
    Admitted.
  End Lemmas.
End EnvDefs.

Section MapKeys.
  Context {A B T : Type}.
  Variable (f : A -> B).
  
  Definition map_keys : t A T -> t B T :=
    List.map (fun '(k, v) => (f k, v)).

  Context {EA : EqDec A eq}.
  Context {EB : EqDec B eq}.
  Hypothesis Hfinj : forall a1 a2, f a1 = f a2 -> a1 = a2.

  Local Hint Extern 0 => simpl_equiv_dec : core.
  Local Hint Extern 0 => simpl_equiv_dec_hyp : core.
  
  Lemma map_keys_find_injective : forall e a,
      find (f a) (map_keys e) = find a e.
  Proof.
    intro e;
      induction e as [| [k v] e IHe];
      intros a; unravel in *; try reflexivity.
    repeat (destruct_if; auto);
      subst; intuition.
  Qed.
End MapKeys.

Section MapVals.
  Context {D U V : Type}.
  Variable (f : U -> V).
  
  Definition map_vals : t D U -> t D V :=
    List.map (fun '(k, v) => (k, f v)).

  Context {R : D -> D -> Prop}.
  Context {RE: Equivalence R}.
  Context {RED: EqDec D R}.

  Local Hint Extern 0 => simpl_equiv_dec : core.
  Local Hint Extern 0 => simpl_equiv_dec_hyp : core.

  Lemma map_vals_find : forall e d,
      find d (map_vals e) = find d e >>| f.
  Proof.
    intro e;
      induction e as [| [k u] e IHe];
      intros d; unravel in *; try reflexivity;
        repeat (destruct_if; auto).
  Qed.
End MapVals.

Module EnvNotations.
  Notation "e1 '⊆' e2"
    := (sub_env e1 e2)
         (at level 80, no associativity) : type_scope.
  Notation "e1 '≝' e2"
    := (eq_env e1 e2)
         (at level 80, no associativity) : type_scope.
  Notation "'!{' env '}!'" := env (env custom p4env at level 99).
  Notation "x" := x (in custom p4env at level 0, x constr at level 0).
  Notation "'∅'" := (empty _ _) (in custom p4env at level 0, no associativity).
  Notation "x ↦ v ';;' e"
    := (bind x v e)
         (in custom p4env at level 40, e custom p4env,
             right associativity).
  Notation "e1 ≪ e2"
           := (scope_shadow e1 e2)
                (in custom p4env at level 41, e1 custom p4env,
                    e2 custom p4env, right associativity).
End EnvNotations.
End Clmt.
