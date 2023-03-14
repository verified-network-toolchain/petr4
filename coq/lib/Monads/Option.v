Require Export Poulet4.Monads.Monad.
From Coq Require Import Lists.List Program.Basics.

Import ListNotations.

Open Scope monad.
Open Scope list_scope.

Definition option_bind (A B: Type) (c: option A) (f: A -> option B) : option B :=
  match c with
  | Some a => f a
  | None => None
  end.

Global Instance option_monad_inst : Monad option :=
  { mret := @Some;
    mbind := option_bind;
  }.

Definition option_fail {A : Type} : option A := None.

Fixpoint reduce_option {A : Type} (acts: list (option A)) (f : A -> A -> A) (base: A) : option A :=
  match acts with
  | nil => Some base
  | None :: _ => None
  | Some x :: xs => reduce_option xs f (f x base)
  end.

Definition guard (b : bool) : option unit := if b then Some tt else None.

Global Hint Unfold option_bind : core.

Lemma sequence_length :
  forall {A : Type} lmao (la : list A),
    sequence lmao = Some la ->
    length lmao = length la.
Proof.
  intros A lmao;
    induction lmao as [| [ama |] lmao IHlmao];
    intros [| a la] H; simpl in *;
    autounfold with * in *;
      try discriminate; auto.
  - destruct (sequence lmao);
      simpl in *; inversion H.
  - destruct (sequence lmao) as [la' |] eqn:Heqlmao;
      simpl in *; inversion H; subst;
        f_equal; auto.
Qed.

Lemma sequence_nil :
  forall (A : Type) (l : list (option A)),
    sequence l = Some [] <-> l = [].
Proof.
  split; destruct l; cbn; unfold option_bind in *; 
  intros; auto; destruct o; try discriminate. 
  destruct (sequence l); discriminate.
Qed.

Lemma sequence_Forall2 : forall {A : Type} lmao (la : list A),
    sequence lmao = Some la ->
    Forall2 (fun mao a => mao = Some a) lmao la.
Proof.
  intros A lmao;
    induction lmao as [| [ama |] lmao IHlmao];
    intros [| a la] H; simpl in *;
      autounfold with * in *;
      try discriminate; auto.
  - destruct (sequence lmao);
      simpl in *; inversion H.
  - destruct (sequence lmao) as [la' |] eqn:Heqlmao;
      simpl in *; inversion H; subst;
        f_equal; auto.
Qed.

Lemma Forall2_sequence : forall {A : Type} lmao (la : list A),
    Forall2 (fun mao a => mao = Some a) lmao la ->
    sequence lmao = Some la.
Proof.
  intros A lmao la H;
    induction H as
      [| mao a lmao la Hala Hlmaola IHlmaola];
    cbn in *; try reflexivity.
  destruct mao as [a' |]; inversion Hala; subst.
  rewrite IHlmaola. reflexivity.
Qed.

Local Hint Resolve sequence_Forall2 : core.
Local Hint Resolve Forall2_sequence : core.

Lemma Forall2_sequence_iff : forall {A : Type} lmao (la : list A),
    Forall2 (fun mao a => mao = Some a) lmao la <->
    sequence lmao = Some la.
Proof.
  intuition.
Qed.

Lemma sequence_map : forall {U V : Type} (f : U -> V) us,
    sequence us >>| List.map f =
    sequence (List.map (lift_monad f) us).
Proof.
  intros U V f us.
  induction us as [| [u |] us IHus]; cbn in *;
    unfold option_bind in *; auto.
  rewrite <- IHus.
  destruct (sequence us) as [sus |]; cbn in *; auto.
Qed.

Lemma map_monad_some :
  forall (A B : Type) (f : A -> option B) (l : list A) (l' : list B),
    map_monad f l = Some l' <-> Forall2 (fun x y => f x = Some y) l l'.
Proof.
  unfold map_monad, "∘". intros. rewrite <- Forall2_sequence_iff.
  rewrite Forall2_map1. reflexivity.
Qed.

(** Proved w/o functional extentionality! *)
Lemma option_map_lift_monad : forall (U V : Type),
    @option_map U V = @lift_monad U V option _.
Proof.
  intros U V.
  unfold option_map, lift_monad, ">>=",
  option_monad_inst, option_bind,mret; reflexivity.
Qed.
(* Print Assumptions option_map_lift_monad. *)

Lemma map_lift_monad_snd_map :
  forall (U V W : Type) (f : V -> option W) (uvs : list (U * V)),
    map
      (lift_monad snd)
      (map (fun '(u,v) => f v >>| pair u) uvs) =
    map f (map snd uvs).
Proof.
  intros U V W f uvs.
  induction uvs as [| [u v] uvs IHuvs];
    cbn in *; f_equal; auto; unfold option_bind;
  destruct (f v) as [w |] eqn:Heqfv; cbn; reflexivity.
Qed.
