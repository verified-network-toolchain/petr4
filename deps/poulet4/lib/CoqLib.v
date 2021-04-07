Require Import Coq.Arith.Arith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Import ListNotations.

Section mergeSort.

  Variable A : Type.
  Variable leb : A -> A -> bool.

  Fixpoint insert (x : A) (ls : list A) : list A :=
    match ls with
    | nil => x :: nil
    | h :: ls' => if leb x h then x :: ls else h :: insert x ls'
    end.

  Fixpoint merge (ls1 ls2 : list A) : list A :=
    match ls1 with
    | nil => ls2
    | h :: ls' => insert h (merge ls' ls2)
    end.

  Fixpoint split (ls : list A) : list A * list A :=
    match ls with
    | nil => (nil, nil)
    | h :: nil => (h :: nil, nil)
    | h1 :: h2 :: ls' => let (ls1, ls2) := split ls' in (h1 :: ls1, h2 :: ls2)
    end.

  Definition lengthOrder (ls1 ls2 : list A) := length ls1 < length ls2.

  Lemma lengthOrder_wf' : forall len, forall ls,
        length ls <= len -> Acc lengthOrder ls.
  Proof.
    induction len; intros; constructor; intros; unfold lengthOrder in * |-.
    - exfalso. destruct ls.
      + simpl in H0. destruct y; simpl in H0; inversion H0.
      + simpl in H; inversion H.
    - apply IHlen. lia.
  Defined.

  Theorem lengthOrder_wf : well_founded lengthOrder.
  Proof. red; intro; eapply lengthOrder_wf'; eauto. Defined.
  
  Lemma split_wf : forall len ls,
      2 <= length ls <= len
      -> let (ls1, ls2) := split ls in lengthOrder ls1 ls /\ lengthOrder ls2 ls.
  Proof.
    unfold lengthOrder. induction len; intros.
    - destruct H. pose proof (Nat.le_trans _ _ _ H H0). inversion H1.
    - destruct H. destruct ls; simpl in H. 1: inversion H. destruct ls.
      1: simpl in H; inversion H; inversion H2. simpl in H.
      destruct (le_lt_dec 2 (length ls)).
      + simpl in H0. assert (2 <= length ls <= len) by lia.
        specialize (IHlen _ H1). simpl. destruct (split ls). simpl. lia.
      + destruct ls. 1: simpl; split; auto. simpl in l. destruct ls.
        1: simpl; split; auto. simpl in l.
        destruct ls; simpl in l; inversion l; inversion H2; inversion H4.
  Qed.

  Ltac split_wf := intros ls ?; intros; generalize (@split_wf (length ls) ls);
                   destruct (split ls); destruct 1.

  Lemma split_wf1 : forall ls, 2 <= length ls -> lengthOrder (fst (split ls)) ls.
  Proof. split_wf. split; auto. auto. Qed.

  Lemma split_wf2 : forall ls, 2 <= length ls -> lengthOrder (snd (split ls)) ls.
  Proof. split_wf. split; auto. auto. Qed.

  Hint Resolve split_wf1 split_wf2: merge_sort.

  Definition mergeSort : list A -> list A.
  Proof.
    refine (Fix lengthOrder_wf (fun _ => list A)
                (fun (ls : list A)
                     (mergeSort : forall ls' : list A,
                         lengthOrder ls' ls -> list A) =>
                   if le_lt_dec 2 (length ls)
                   then let lss := split ls in
                        merge (mergeSort (fst lss) _) (mergeSort (snd lss) _)
                   else ls)); subst lss; eauto with merge_sort.
  Defined.

  Theorem mergeSort_eq : forall ls,
      mergeSort ls =
      if le_lt_dec 2 (length ls)
      then let lss := split ls in
           merge (mergeSort (fst lss)) (mergeSort (snd lss))
      else ls.
  Proof.
    intros; apply (Fix_eq lengthOrder_wf (fun _ => list A)). intros.
    destruct (le_lt_dec 2 (length x)); simpl; f_equal; auto.
  Qed.
  
End mergeSort.

Arguments mergeSort {_} _ _.


Definition ascii_leb (c1 c2: ascii) := BinNat.N.leb (N_of_ascii c1) (N_of_ascii c2).

Fixpoint string_leb (s1 s2: string) :=
  match s1, s2 with
  | EmptyString, EmptyString => true
  | String c1 s1, String c2 s2 =>
    if (c1 =? c2)%char then string_leb s1 s2 else ascii_leb c1 c2
  | EmptyString, String _ _ => true
  | String _ _, EmptyString => false
  end.

Eval vm_compute in string_leb "abcd" "abcde".

Local Open Scope string_scope.

Eval vm_compute in
    mergeSort string_leb ["Bob"; "Alice"; "Tom"; "Jinn"; "Jin"; "Carol"].
