Require Import Poulet4.Monads.Monad.

Open Scope monad.
Open Scope list_scope.


Definition option_monad {Result: Type} :=
  option Result.

Definition option_ret (A: Type) (a: A) : option_monad := Some a.

Definition option_bind (A B: Type) (c: @option_monad A) (f: A -> @option_monad B) : option_monad :=
  match c with
  | Some a => f a
  | None => None
  end.

Global Instance option_monad_inst : Monad option :=
  { mret := option_ret;
    mbind := option_bind;
  }.

Definition option_fail {A : Type} : @option_monad A := None.

Fixpoint reduce_option {A : Type} (acts: list (option A)) (f : A -> A -> A) (base: A) : option A :=
  match acts with
  | nil => Some base
  | None :: _ => None
  | Some x :: xs => reduce_option xs f (f x base)
  end.

Global Hint Unfold option_ret option_bind : core.

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

Require Import Lists.List.

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
