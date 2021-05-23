Require Import Coq.Arith.Arith.
Require Import Coq.NArith.NArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Import ListNotations.

Section mergeSort.

  Variable A : Type.
  Variable leb : A -> A -> bool.
  Hypothesis leb_trans:
    forall x y z, leb x y = true -> leb y z = true -> leb x z = true.
  Hypothesis leb_total: forall x y, leb x y = true \/ leb y x = true.

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

  Fixpoint splitL (ls : list A) : list A * list A :=
    match ls with
    | nil => (nil, nil)
    | h :: nil => (h :: nil, nil)
    | h1 :: h2 :: ls' => let (ls1, ls2) := splitL ls' in (h1 :: ls1, h2 :: ls2)
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

  Lemma splitL_wf : forall len ls,
      2 <= length ls <= len
      -> let (ls1, ls2) := splitL ls in lengthOrder ls1 ls /\ lengthOrder ls2 ls.
  Proof.
    unfold lengthOrder. induction len; intros.
    - destruct H. pose proof (Nat.le_trans _ _ _ H H0). inversion H1.
    - destruct H. destruct ls; simpl in H. 1: inversion H. destruct ls.
      1: simpl in H; inversion H; inversion H2. simpl in H.
      destruct (le_lt_dec 2 (length ls)).
      + simpl in H0. assert (2 <= length ls <= len) by lia.
        specialize (IHlen _ H1). simpl. destruct (splitL ls). simpl. lia.
      + destruct ls. 1: simpl; split; auto. simpl in l. destruct ls.
        1: simpl; split; auto. simpl in l.
        destruct ls; simpl in l; inversion l; inversion H2; inversion H4.
  Qed.

  Ltac splitL_wf := intros ls ?; intros; generalize (@splitL_wf (length ls) ls);
                    destruct (splitL ls); destruct 1.

  Lemma splitL_wf1 : forall ls, 2 <= length ls -> lengthOrder (fst (splitL ls)) ls.
  Proof. splitL_wf. split; auto. auto. Qed.

  Lemma splitL_wf2 : forall ls, 2 <= length ls -> lengthOrder (snd (splitL ls)) ls.
  Proof. splitL_wf. split; auto. auto. Qed.

  Hint Resolve splitL_wf1 splitL_wf2: merge_sort.

  Definition mergeSort : list A -> list A.
  Proof.
    refine (Fix lengthOrder_wf (fun _ => list A)
                (fun (ls : list A)
                     (mergeSort : forall ls' : list A,
                         lengthOrder ls' ls -> list A) =>
                   if le_lt_dec 2 (length ls)
                   then let lss := splitL ls in
                        merge (mergeSort (fst lss) _) (mergeSort (snd lss) _)
                   else ls)); subst lss; eauto with merge_sort.
  Defined.

  Theorem mergeSort_eq : forall ls,
      mergeSort ls =
      if le_lt_dec 2 (length ls)
      then let lss := splitL ls in
           merge (mergeSort (fst lss)) (mergeSort (snd lss))
      else ls.
  Proof.
    intros; apply (Fix_eq lengthOrder_wf (fun _ => list A)). intros.
    destruct (le_lt_dec 2 (length x)); simpl; f_equal; auto.
  Qed.

  (** *Permutation property *)

  Lemma insert_perm: forall x l, Permutation (x :: l) (insert x l).
  Proof.
    intros. induction l.
    - simpl. auto.
    - simpl. destruct (leb x a); auto. apply perm_trans with (a :: x :: l).
      + constructor.
      + apply perm_skip. apply IHl.
  Qed.

  Lemma merge_perm: forall l1 l2, Permutation (l1 ++ l2) (merge l1 l2).
  Proof.
    induction l1; intros; simpl; auto. apply perm_trans with (a :: merge l1 l2).
    - now apply perm_skip.
    - apply insert_perm.
  Qed.

  Lemma splitL_perm: forall l l1 l2, splitL l = (l1, l2) -> Permutation l (l1 ++ l2).
  Proof.
    intro l. remember (length l) as n. assert (length l <= n) by lia.
    clear Heqn. revert l H. induction n; intros.
    - destruct l.
      + simpl in H0. inversion H0. simpl. auto.
      + simpl in H. exfalso; lia.
    - destruct l. 1: simpl in H0; inversion H0; simpl; auto.
      destruct l; simpl in H0; simpl in H.
      + inversion H0; simpl; auto.
      + destruct n. 1: exfalso; lia.
        destruct (splitL l) as [l1' l2'] eqn: ?H. inversion H0. subst.
        assert (length l <= S n) by lia. specialize (IHn l H2 _ _ H1).
        simpl. apply perm_skip. now apply Permutation_cons_app.
  Qed.

  Lemma splitL_length: forall l l1 l2,
      splitL l = (l1, l2) -> length l1 <= length l /\ length l2 <= length l.
  Proof.
    intros. apply splitL_perm in H. apply Permutation_length in H.
    rewrite app_length in H. lia.
  Qed.

  Theorem mergeSort_perm: forall l, Permutation l (mergeSort l).
  Proof.
    intro l. remember (length l) as n. assert (length l <= n) by lia. clear Heqn.
    revert l H. induction n; intros.
    - destruct l.
      + rewrite mergeSort_eq. simpl; auto.
      + simpl in H. exfalso; lia.
    - rewrite mergeSort_eq. do 2 (destruct l; [simpl; auto|]).
      simpl. destruct (splitL l) as [l1 l2] eqn:?H. simpl.
      pose proof (splitL_length _ _ _ H0). destruct H1. simpl in H.
      assert (length (a :: l1) <= n) by (simpl; lia).
      assert (length (a0 :: l2) <= n) by (simpl; lia). apply IHn in H3, H4.
      apply perm_trans with (mergeSort (a :: l1) ++ mergeSort (a0 :: l2)).
      2: apply merge_perm. apply splitL_perm in H0.
      apply perm_trans with ((a :: l1) ++ (a0 :: l2)).
      + simpl. constructor. now apply Permutation_cons_app.
      + now apply Permutation_app.
  Qed.

  (** *Sorted property *)

  Inductive Sorted: list A -> Prop :=
  | Sorted_nil: Sorted nil
  | Sorted_cons: forall hd tl, (forall x, In x tl -> leb hd x = true) ->
                               Sorted tl -> Sorted (hd :: tl).

  Lemma insert_in: forall x y l, In x (insert y l) -> y = x \/ In x l.
  Proof.
    intros. apply in_inv. apply Permutation_in with (insert y l); auto.
    apply Permutation_sym. apply insert_perm.
  Qed.

  Lemma leb_false: forall x y, leb x y = false -> leb y x = true.
  Proof. intros. destruct (leb_total x y); auto. rewrite H in H0. discriminate. Qed.

  Lemma insert_sorted: forall x l, Sorted l -> Sorted (insert x l).
  Proof.
    intros. induction l; simpl.
    - constructor; auto.
    - destruct (leb x a) eqn:?H.
      + constructor; auto. intros y ?. apply in_inv in H1. destruct H1. 1: now subst.
        inversion H; subst. specialize (H4 _ H1). eapply leb_trans; eauto.
      + inversion H; subst. constructor. 2: now apply IHl. intros y ?.
        apply insert_in in H1. destruct H1. 2: now apply H3.
        subst. now apply leb_false.
  Qed.

  Lemma merge_sorted: forall l1 l2, Sorted l1 -> Sorted l2 -> Sorted (merge l1 l2).
  Proof.
    induction l1; intros; simpl; auto. apply insert_sorted. apply IHl1; auto.
    now inversion H.
  Qed.

  Lemma mergeSort_sorted: forall l, Sorted (mergeSort l).
  Proof.
    intro l. remember (length l) as n. assert (length l <= n) by lia. clear Heqn.
    revert l H. induction n; intros.
    - destruct l.
      + rewrite mergeSort_eq. simpl. constructor.
      + simpl in H. exfalso; lia.
    - rewrite mergeSort_eq. do 2 (destruct l; [simpl; constructor |]).
      + intros. inversion H0.
      + constructor.
      + simpl. destruct (splitL l) as [l1 l2] eqn:?H. simpl.
        pose proof (splitL_length _ _ _ H0). destruct H1. simpl in H.
        assert (length (a :: l1) <= n) by (simpl; lia).
        assert (length (a0 :: l2) <= n) by (simpl; lia). apply IHn in H3, H4.
        now apply merge_sorted.
  Qed.

End mergeSort.

Arguments mergeSort {_} _ _.

Definition ascii_leb (c1 c2: ascii) := N.leb (N_of_ascii c1) (N_of_ascii c2).

Lemma ascii_leb_total: forall c1 c2, ascii_leb c1 c2 = true \/ ascii_leb c2 c1 = true.
Proof.
  intros. unfold ascii_leb. remember (N_of_ascii c1) as n1.
  remember (N_of_ascii c2) as n2. clear c1 c2 Heqn1 Heqn2.
  destruct (N.leb n1 n2) eqn:?H. left; auto. right.
  apply N.leb_gt in H. rewrite N.leb_le.
  red. red in H. rewrite H. discriminate.
Qed.

Lemma ascii_leb_trans: forall c1 c2 c3,
    ascii_leb c1 c2 = true -> ascii_leb c2 c3 = true -> ascii_leb c1 c3 = true.
Proof.
  unfold ascii_leb. intros. rewrite N.leb_le in *. etransitivity; eauto.
Qed.

Lemma N_of_digits_unique: forall l1 l2,
    length l1 = length l2 -> N_of_digits l1 = N_of_digits l2 -> l1 = l2.
Proof.
  induction l1; intros; destruct l2; auto.
  - inversion H.
  - inversion H.
  - simpl in H0. simpl in H. assert (length l1 = length l2) by lia.
    specialize (IHl1 _ H1). clear H. remember (N_of_digits l1) as n1.
    remember (N_of_digits l2) as n2. destruct n1, n2.
    + simpl in H0. rewrite !N.add_0_r in H0.
      destruct a, b; try discriminate; f_equal; apply IHl1; auto.
    + clear -H0. exfalso. destruct a, b; lia.
    + clear -H0. exfalso. destruct a, b; lia.
    + destruct a, b; try (exfalso; lia); f_equal; apply IHl1; lia.
Qed.

Lemma N_of_ascii_unique: forall c1 c2, N_of_ascii c1 = N_of_ascii c2 -> c1 = c2.
Proof.
  unfold N_of_ascii. intros. destruct c1, c2.
  apply N_of_digits_unique in H.
  - inversion H. subst. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma ascii_leb_eq: forall c1 c2,
    ascii_leb c1 c2 = true -> ascii_leb c2 c1 = true -> c1 = c2.
Proof.
  unfold ascii_leb. intros. rewrite N.leb_le in H, H0.
  apply N_of_ascii_unique. lia.
Qed.

Fixpoint string_leb (s1 s2: string) :=
  match s1, s2 with
  | EmptyString, EmptyString => true
  | String c1 s1, String c2 s2 =>
    if (c1 =? c2)%char then string_leb s1 s2 else ascii_leb c1 c2
  | EmptyString, String _ _ => true
  | String _ _, EmptyString => false
  end.

Lemma string_leb_total: forall s1 s2,
    string_leb s1 s2 = true \/ string_leb s2 s1 = true.
Proof.
  induction s1; intros.
  - left. simpl. destruct s2; auto.
  - destruct s2.
    + right. simpl. auto.
    + simpl. destruct ((a =? a0)%char) eqn:?H.
      * rewrite Ascii.eqb_sym in H. rewrite H. apply IHs1.
      * rewrite Ascii.eqb_neq in H. apply not_eq_sym in H.
        rewrite <- Ascii.eqb_neq in H. rewrite H. apply ascii_leb_total.
Qed.

Lemma string_leb_trans: forall s1 s2 s3,
    string_leb s1 s2 = true -> string_leb s2 s3 = true -> string_leb s1 s3 = true.
Proof.
  induction s1; intros.
  - simpl. destruct s3; auto.
  - destruct s2; simpl in H. 1: discriminate. destruct s3; simpl in H0.
    1: discriminate. simpl. destruct ((a =? a0)%char) eqn:?H.
    + rewrite Ascii.eqb_eq in H1. subst a0. destruct ((a =? a1)%char); auto.
      now apply IHs1 with s2.
    + destruct ((a0 =? a1)%char) eqn:?H.
      * rewrite Ascii.eqb_eq in H2. subst a1. now rewrite H1.
      * rewrite Ascii.eqb_neq in H1, H2. cut ((a =? a1)%char = false); intros.
        -- rewrite H3. eapply ascii_leb_trans; eauto.
        -- rewrite Ascii.eqb_neq. intro. subst a1. apply H1. now eapply ascii_leb_eq.
Qed.

Eval vm_compute in string_leb "abcd" "abcde".

Local Open Scope string_scope.

Eval vm_compute in
    mergeSort string_leb ["Bob"; "Alice"; "Tom"; "Jinn"; "Jin"; "Carol"].

Definition findi {A: Type} (f: A -> bool) (l: list A): option (nat * A) :=
  let fix iter (al: list A) (index: nat): option (nat * A) :=
      match al with
      | [] => None
      | a :: rest => if f a then Some (index, a) else iter rest (S index)
      end in
  iter l O.

(* Eval vm_compute in findi (Nat.eqb 5) [1; 2; 5; 6; 3]. *)

(* Eval vm_compute in nth_error [1; 2; 5; 6; 3] 2.  *)
