Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Poulet4.P4cub.Util.EquivUtil.
Import ListNotations.

Module FuncAsMap.

  Section FuncAsMap.

    Context {key: Type}.
    Context {key_eqb: key -> key -> bool}.
    Context {value: Type}.

    Definition t := key -> option value.

    Definition empty: t := fun _ => None.
    Definition get: key -> t -> option value := fun k fmap => fmap k.
    Definition set: key -> value -> t -> t :=
      fun k v fmap x => if key_eqb x k then Some v else fmap x.
    Definition remove (ky : key) (fmap : t) : t :=
      fun k => if key_eqb k ky then None else fmap k.
    
    Definition sets: list key -> list value -> t -> t :=
      fun kList vList fmap =>
        fold_left (fun fM kvPair => set (fst kvPair) (snd kvPair) fM)
                  (combine kList vList) fmap.

    Definition gets (kl: list key) (m: t): list (option value) :=
      map (fun k => get k m) kl.

    Definition removes (ks : list key) (m : t) : t :=
      List.fold_right remove m ks.

    Lemma get_set_same:
      forall k v m, (forall k, key_eqb k k = true) -> get k (set k v m) = Some v.
    Proof. intros. unfold set, get. now rewrite H. Qed.

    Lemma get_set_diff:
      forall k k' v m, (forall k k', k <> k' -> key_eqb k k' = false) ->
                       k <> k' -> get k (set k' v m) = get k m.
    Proof. intros. unfold set, get. specialize (H _ _ H0). now rewrite H. Qed.

  End FuncAsMap.

  Section FuncMapMap.
    Context {key: Type} {key_eqb: key -> key -> bool} {U V : Type}.

    Section Map.
      Variable f : U -> V.
      
      Definition map_map (e : @t key U) : @t key V :=
        fun k => match e k with
            | Some u => Some (f u)
            | None   => None
              end.
    End Map.

    Section Rel.
      Variable R : U -> V -> Prop.

      Definition related (eu : @t key U) (ev : @t key V) : Prop :=
        forall k : key,
          relop R (get k eu) (get k ev).
    End Rel.
  End FuncMapMap.
End FuncAsMap.

Module IdentMap.

Section IdentMap.

Notation ident := String.string.
Context {A: Type}.

Definition t := @FuncAsMap.t ident A.
Definition empty : t := FuncAsMap.empty.
Definition get : ident -> t -> option A := FuncAsMap.get.
Definition set : ident -> A -> t -> t :=
  @FuncAsMap.set ident String.eqb A.
Definition remove : ident -> t -> t :=
  @FuncAsMap.remove ident String.eqb A.
Definition sets: list ident -> list A -> t -> t :=
  @FuncAsMap.sets ident String.eqb A.
Definition gets: list ident -> t -> list (option A) := FuncAsMap.gets.
Definition removes : list ident -> t -> t :=
  @FuncAsMap.removes ident String.eqb A.
End IdentMap.

End IdentMap.

Definition list_eqb {A} (eqb : A -> A -> bool) al bl :=
  ListUtil.list_eq eqb al bl.

Definition path_eqb :
  (list String.string) -> (list String.string) -> bool :=
  list_eqb String.eqb.

Lemma path_eqb_refl: forall k, path_eqb k k = true.
Proof.
  intros. unfold path_eqb. induction k; simpl; auto.
  rewrite IHk. rewrite String.eqb_refl. now simpl.
Qed.

Lemma path_eqb_neq: forall k k', k <> k' -> path_eqb k k' = false.
Proof.
  induction k, k'; intros; unfold path_eqb; simpl; auto.
  - exfalso. now apply H.
  - destruct (String.eqb a s) eqn:?; simpl; auto.
    rewrite IHk; auto. rewrite String.eqb_eq in Heqb. intro. apply H. now subst.
Qed.

Module PathMap.

Section PathMap.

Notation ident := String.string.
Notation path := (list ident).
Context {A: Type}.

Definition t := @FuncAsMap.t path A.
Definition empty : t := FuncAsMap.empty.
Definition get : path -> t -> option A := FuncAsMap.get.
Definition set : path -> A -> t -> t :=
  @FuncAsMap.set path path_eqb A.
Definition remove : path -> t -> t :=
  @FuncAsMap.remove path path_eqb A.
Definition sets : list path -> list A -> t -> t :=
  @FuncAsMap.sets path path_eqb A.
Definition gets: list path -> t -> list (option A) := FuncAsMap.gets.
Definition removes : list path -> t -> t :=
  @FuncAsMap.removes path path_eqb A.

Lemma get_set_same: forall k v m, get k (set k v m) = Some v.
Proof. intros. apply FuncAsMap.get_set_same. apply path_eqb_refl. Qed.

Lemma get_set_diff:
  forall k k' v m, k <> k' -> get k (set k' v m) = get k m.
Proof. intros. apply FuncAsMap.get_set_diff; auto. apply path_eqb_neq. Qed.

End PathMap.

End PathMap.

Arguments IdentMap.t _: clear implicits.
Arguments PathMap.t _: clear implicits.
