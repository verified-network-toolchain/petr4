Require Import String List.
Require Export Poulet4.Monads.Monad.

Inductive result (Err A : Type) : Type :=
| Ok  : A -> result Err A
| Error : Err -> result Err A.
Arguments Ok {Err A}.
Arguments Error {Err A}.

Definition ok {Err A : Type} (x : A) : result Err A := Ok x.
Definition error {Err A : Type} (err : Err) : result Err A := Error err.

Definition is_ok {Err A : Type} (x : result Err A) : Prop :=
  match x with
  | Ok x => True
  | _ => False
  end.

Definition is_okb {Err A : Type} (x : result Err A) : bool :=
  match x with
  | Ok x => true
  | _ => false
  end.

Definition is_error {Err A: Type} (x : result Err A) : Prop :=
  match x with
  | Error x => True
  | _ => False
  end.

Definition bind {Err A B : Type} (r : result Err A)  (f : A -> result Err B) : result Err B :=
  match r with
  | Error err => Error err
  | Ok x => f x
  end.

Global Instance result_monad_inst (Err: Type) : Monad (result Err) :=
  { mret := fun _ v => ok v;
    mbind := fun _ _ c1 c2 => bind c1 c2 }.

Definition opt_bind {Err A B : Type} (r : option A) (err : Err) (f : A -> result Err B) : result Err B :=
  match r with
  | None => error err
  | Some x => f x
  end.

Definition from_opt {Err A} (r : option A) (err : Err) :=
  match r with
  | None => error err
  | Some a => ok a
  end.

Definition from_sum {Err A} (r : Err + A) : result Err A :=
  match r with
  | inl err => error err
  | inr a => ok a
  end.

Definition to_opt {Err A} (r : result Err A) : option A :=
  match r with
  | Ok x => Some x
  | Error _ => None
  end.

Definition map {Err A B : Type} (f : A -> B)  (r : result Err A) : result Err B :=
  match r with
  | Error err => error err
  | Ok x => ok (f x)
  end.

Definition emap {Err Err' A : Type} (f : Err -> Err') (r : result Err A) : result Err' A :=
  match r with
  | Error err => error (f err)
  | Ok x => ok x
  end.

Definition overwritebind {Err A B : Type} (r : result Err A) (err : Err) (f : A -> result Err B) : result Err B :=
  match r with
  | Error err => error err (* ++ " because: \n" ++ s)*)
  | Ok x  => f x
  end.

Definition rbindcomp {Err A B C : Type} (f : B -> C) (g : A -> result Err B) (a : A) : result Err C :=
  map f (g a).

Definition rcomp {Err A B C : Type} (f : B -> result Err C) (g : A -> result Err B) (a : A) : result Err C :=
  bind (g a) f.

Fixpoint rred_aux {Err A : Type} (os : list (result Err A)) (acc : result Err (list A)) : result Err (list A) :=
  match acc with
  | Error err => error err
  | Ok acc =>
    match os with
    | Error err :: _ => error err
    | Ok x :: os =>
      rred_aux os (ok (x :: acc))
    | _ => ok acc
    end
  end.

Definition rred {Err A : Type} (os : list (result Err A)) : result Err (list A) :=
  match rred_aux os (ok nil) with
  | Error err => error err
  | Ok xs => ok (List.rev' xs)
  end.

Definition res_snd {Err A B : Type} (p : A * result Err B) : result Err (A * B) :=
  match p with
  | (_, Error err) => error err
  | (a, Ok b) => ok (a, b)
  end.

Definition
  snd_res_map {Err A B C : Type}
  (f : B -> result Err C) '((x,y) : A * B) : result Err (A * C) :=
  map (pair x) (f y).

Module ResultNotations.
  Notation "'let+' p ':=' c1 'in' c2" := (map (fun p => c2) c1)
                                            (at level 61, p as pattern, c1 at next level, right associativity).

  Notation "'let*~' p ':=' c1 'else' str 'in' c2 " := (opt_bind c1 str (fun p => c2))
                                                        (at level 61, p as pattern, c1 at next level, right associativity).

  Notation "'let~' p ':=' c1 'over' str 'in' c2" := (overwritebind c1 str (fun p => c2))
                                                      (at level 61, p as pattern, c1 at next level, right associativity).

  Infix ">>=>" := rbindcomp (at level 80, right associativity).

  Infix ">=>" := rcomp (at level 80, right associativity).

  Infix "|=>" := (fun r f => map f r) (at level 80, right associativity).

End ResultNotations.

Definition cons_res {Err A : Type} (hd_res : result Err A) (rlist : result Err (list A)) : result Err (list A) :=
  let* l := rlist in
  map (fun p => p :: l) hd_res.

Fixpoint commute_result_optlist {A : Type} (l : list (option (result string A))) : result string (list (option A)) :=
  match l with
  | nil => ok nil
  | o :: l =>
      let* l := commute_result_optlist l in
      match o with
      | None =>
          ok (None :: l)
      | Some a_res =>
          map (fun p => Some p :: l) a_res
      end
  end.

  Lemma ok_Ok_inj :
    forall {Err A : Type} (a a': A),
      @ok Err A a = @Ok Err A a' ->
      a = a'.
  Proof.
    unfold ok.
    intros.
    injection H.
    tauto.
  Qed.

  Lemma error_not_ok :
    forall {Err A : Type} (e : Err) (a: A),
      @error Err A e = @Ok Err A a ->
      False.
  Proof.
    unfold error.
    congruence.
  Qed.

  Lemma from_opt_Ok :
    forall {Err A : Type} (c : option A) (e : Err) (v : A),
      from_opt c e = Ok v ->
      c = Some v.
  Proof.
    unfold from_opt.
    intros.
    destruct c.
    - apply ok_Ok_inj in H.
      congruence.
    - exfalso; eauto using error_not_ok.
  Qed.

  Lemma bind_Ok :
    forall {Err A B : Type}
           (c : result Err A)
           (f : A -> result Err B)
           (v : B),
      bind c f = Ok v ->
      exists w,
        c = Ok w /\ f w = Ok v.
  Proof.
    unfold bind.
    intros.
    destruct c; eauto.
    congruence.
  Qed.

  Ltac unchecked_inv_bind H :=
  let w := fresh "w" in
  let Hw := fresh "Hw" in
  apply bind_Ok in H;
  destruct H as [w [Hw H]].

Ltac inv_bind H :=
  match type of H with
  | mbind ?c ?f = Ok ?v =>
      unchecked_inv_bind H
  | bind ?c ?f = Ok ?v =>
      unchecked_inv_bind H
  end.

Lemma map_Ok :
  forall {Err A B : Type}
         (f : A -> B)
         (c : result Err A)
         (v : B),
    map f c = Ok v ->
    exists w,
      c = Ok w /\ v = f w.
Proof.
  unfold map.
  intros.
  destruct c.
  - apply ok_Ok_inj in H.
    eauto.
  - apply error_not_ok in H.
    tauto.
Qed.

Ltac unchecked_inv_map H :=
  let w := fresh "w" in
  let Hw := fresh "Hw" in
  apply map_Ok in H;
  destruct H as [w [Hw H]].

Ltac inv_map H :=
  match type of H with
  | map ?c ?f = Ok ?v =>
      unchecked_inv_map H
  end.

Ltac simpl_from_opt H :=
  apply from_opt_Ok in H.

Ltac simpl_result_error H :=
  apply error_not_ok in H.

Ltac simpl_result_ok H :=
  apply ok_Ok_inj in H.


Tactic Notation "simpl_to_opt" "as" simple_intropattern(E) :=
  match goal with
  | H: to_opt ?r = Some _ |- _ => destruct r eqn:E; try discriminate
  end.

Tactic Notation "simpl_to_opt" := simpl_to_opt as ?.

Ltac simpl_result H :=
  inv_bind H ||
  inv_map H ||
  simpl_from_opt H ||
  simpl_result_error H ||
  simpl_result_ok H ||
  idtac.

Ltac simpl_result_all :=
  match goal with
  | H: _ |- _ => progress simpl_result H
  end.

Lemma sequence_map_Result_ok : forall {Err A} (l : list A),
    sequence (List.map ok l) = ok (Err := Err) l.
Proof.
  intros; induction l as [| a l ih]; cbn; auto.
  rewrite ih; reflexivity.
Qed.

Lemma sequence_length :
  forall {Err A : Type} lmao (la : list A),
    sequence lmao = Ok (Err := Err) la ->
    length lmao = length la.
Proof.
  intros Err A lmao.
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

Lemma sequence_Forall2 : forall {Err A : Type} lmao (la : list A),
    sequence lmao = Ok (Err := Err) la ->
    Forall2 (fun mao a => mao = Ok a) lmao la.
Proof.
  intros Err A lmao;
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
