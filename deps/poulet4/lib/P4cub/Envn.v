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
        find x e = find x (bind y v e).
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
