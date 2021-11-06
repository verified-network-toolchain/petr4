Require Import Poulet4.P4cub.Util.Utiliser.

Declare Custom Entry p4env.

(** * Environments *)
Module Env.

(** Definition of environments. *)
Definition t (D T : Type) : Type := list (D * T).

(** The empty environment. *)
Definition empty (D T : Type) : t D T := nil.

Section EnvDefs.
  Context {D T : Type}.

  Context {equiv_rel : D -> D -> Prop}.

  Context {HEquiv : Equivalence equiv_rel}.

  Context {HE : EqDec D equiv_rel}.

  (** Looking up values in the environment. *)
  Fixpoint find (x: D) (e: t D T) : option T :=
    match e with
    | nil => None
    | (y, v) :: e' =>
      if HE x y
      then Some v
      else find x e'
    end.
  (**[]*)

  (** Updating the environment. *)
  Definition bind (x : D) (v : T) (e : t D T) : t D T :=
    (x, v) :: e.
  (**[]*)

  (** Scope Shadowing, [e1] shadows [e2]. *)
  Definition scope_shadow (e1 e2 : t D T) : t D T :=
    e1 ++ e2.
  (**[]*)
  
  (** Gather values given a list of keys. *)
  Definition gather (e: t D T) : list D -> list T :=
    List.fold_right
      (fun k acc =>
         match find k e with
         | Some v => v :: acc
         | None => acc
         end) [].
  
  Fixpoint keys (e: t D T) : list D := 
    match e with 
    | nil => nil
    | (y, v) :: e' =>
      let keys' := keys e' in 
      match find y e' with
      | None => y::keys'
      | _ => keys'
      end
    end.

  Definition sub_env (e1 e2 : t D T) : Prop :=
    forall k v,
      find k e1 = Some v -> find k e2 = Some v.

  Definition eq_env (e1 e2 : t D T) : Prop :=
    sub_env e1 e2 /\ sub_env e2 e1.
  
  Section Lemmas.
    Local Hint Extern 0 => simpl_equiv_dec : core.
    Local Hint Extern 0 => simpl_equiv_dec_hyp : core.
    
    Lemma bind_sound : forall x v e,
      find x (bind x v e) = Some v.
    Proof.
      intros; simpl; auto.
    Qed.
    
    Lemma bind_complete : forall x y v e,
        ~ equiv_rel x y ->
        find x (bind y v e) = find x e.
    Proof.
      intros; simpl; auto.
    Qed.

    Lemma bind_twice : forall x y v v' e,
        find y (bind x v (bind x v' e)) = find y (bind x v e).
    Proof.
      intros; simpl; destruct_if; auto.
    Qed.

    Lemma bind_diff_comm : forall x y z u v e,
        ~ equiv_rel x y ->
        find z (bind x u (bind y v e)) = find z (bind y v (bind x u e)).
    Proof.
      intros; simpl;
        repeat (destruct_if; auto).
      assert (equiv_rel x z) by (symmetry; assumption).
      assert (equiv_rel x y) by (etransitivity; eauto).
      contradiction.
    Qed.

    Lemma in_keys_find : forall e k,
        In k (keys e) -> exists v, find k e = Some v.
    Proof.
      induction e as [| [k vl] e IHe];
        intros ky Hky; simpl in *; try contradiction.
      destruct (HE ky k); unravel in *; eauto.
      destruct (find k e) as [v' |] eqn:Hfind;
        unravel in *; intuition; subst; intuition.
    Qed.

    Lemma find_in_keys : forall e k v,
        find k e = Some v -> exists k', equiv_rel k k' /\ In k' (keys e).
    Proof.
      intro e; induction e as [| [k v] e IHe];
        intros ky vl Hkyvl; simpl in *; try discriminate.
      destruct (HE ky k); unravel in *.
      - inv Hkyvl.
        destruct (find k e) as [v' |] eqn:Hfind.
        + apply IHe in Hfind as (k' & Hkk' & HInk').
          exists k'. intuition. transitivity k; assumption.
        + exists k. intuition.
      - destruct (find k e) as [v' |] eqn:Hfind;
          apply IHe in Hkyvl as (k' & Hkk' & HInk'); firstorder.
    Qed.

    Lemma find_equiv_rel : forall e k1 k2,
        equiv_rel k1 k2 -> find k1 e = find k2 e.
    Proof.
      intro e; induction e as [| [k v] e IHe];
        intros k1 k2 Heq; simpl in *; auto.
      destruct (HE k1 k) as [Hk1k | Hk1k];
        destruct (HE k2 k) as [Hk2k | Hk2k];
        unravel in *;
        try (rewrite Heq in Hk1k; contradiction);
        auto.
    Qed.

    Lemma find_none_not_in_keys : forall e k,
        find k e = None -> ~ In k (keys e).
    Proof.
      intros e k Hfind Hin.
      apply in_keys_find in Hin as (v & Hv).
      rewrite Hfind in Hv. discriminate.
    Qed.
    
    Lemma not_in_keys_find : forall e k,
        ~ In k (keys e) -> find k e = None.
    Proof.
      intro e; induction e as [| [k v] e IHe];
        intros ky Hky; unravel in *; auto.
      destruct (find k e) as [vl |] eqn:Hfind;
        destruct (HE ky k) as [Hkyk | Hkyk]; unravel in *; auto.
      - apply IHe in Hky.
        apply find_equiv_rel with (e := e) in Hkyk.
        rewrite Hkyk in Hky.
        rewrite Hky in Hfind. discriminate.
      - apply Decidable.not_or in Hky as [Hkky Hkye].
        apply IHe in Hkye.
    Abort.
    
    Global Instance sub_env_reflexive : Reflexive sub_env.
    Proof. firstorder. Qed.

    Global Instance sub_env_transitive : Transitive sub_env.
    Proof. firstorder. Qed.

    Global Instance eq_env_reflexive : Reflexive eq_env.
    Proof. firstorder. Qed.

    Global Instance eq_env_symmetric : Symmetric eq_env.
    Proof. firstorder. Qed.

    Global Instance eq_env_transitive : Transitive eq_env.
    Proof. firstorder. Qed.

    Global Instance eq_env_equivalence : Equivalence eq_env.
    Proof. firstorder. Qed.
    
    Global Instance sub_env_antisymmetric
      : @Antisymmetric _ _ eq_env_equivalence sub_env.
    Proof. firstorder. Qed.


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
        sub_env e (bind k v e) -> find k e = None.
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
End Env.
