Require Import Coq.Strings.String
        Poulet4.P4cub.Util.FunUtil
        Coq.Numbers.DecimalString.
Require Coq.Lists.List.

Local Open Scope string_scope.

(* Ripped from Software foundations : https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html *)
Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match Nat.modulo n 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
  | 0 => acc'
  | S time' =>
    match Nat.div n 10 with
    | 0 => acc'
    | n' => string_of_nat_aux time' n' acc'
    end
  end.

Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n "".

Lemma list_of_string_append : forall s1 s2 : string,
    list_ascii_of_string (s1 ++ s2) =
    List.app (list_ascii_of_string s1) (list_ascii_of_string s2).
Proof.
  intro s1; induction s1 as [| a1 s1 IHs1]; intro s2;
    simpl in *; f_equal; auto.
Qed.

Lemma string_of_list_append : forall l1 l2 : list Ascii.ascii,
    string_of_list_ascii (List.app l1 l2) =
    string_of_list_ascii l1 ++ string_of_list_ascii l2.
Proof.
  intro l1; induction l1 as [| a1 l1 IHl1]; intro l2;
    simpl in *; f_equal; auto.
Qed.

Lemma list_ascii_of_string_inj : forall s1 s2,
    list_ascii_of_string s1 = list_ascii_of_string s2 -> s1 = s2.
Proof.
  intro s1; induction s1 as [| a1 s1 IHs1];
    intros [| a2 s2] H; simpl in *; inv H; f_equal; auto.
Qed.

Lemma string_of_list_ascii_inj : forall l1 l2,
    string_of_list_ascii l1 = string_of_list_ascii l2 -> l1 = l2.
Proof.
  intro l1; induction l1 as [| a1 l1 IHl1];
    intros [| a2 l2] H; simpl in *; inv H; f_equal; auto.
Qed.

Lemma string_append_inj_l : forall s s1 s2 : string,
    s ++ s1 = s ++ s2 -> s1 = s2.
Proof.
  intros s s1 s2 H.
  apply list_ascii_of_string_inj.
  apply f_equal with (f := list_ascii_of_string) in H.
  repeat rewrite list_of_string_append in H.
  eauto using List.app_inv_head.
Qed.

Lemma string_append_inj_r : forall s1 s2 s : string,
    s1 ++ s = s2 ++ s -> s1 = s2.
Proof.
  intros s1 s2 s H.
  apply list_ascii_of_string_inj.
  apply f_equal with (f := list_ascii_of_string) in H.
  repeat rewrite list_of_string_append in H.
  eauto using List.app_inv_tail.
Qed.

Lemma empty_string_of_uint : forall a b,
    NilEmpty.string_of_uint a = NilEmpty.string_of_uint b -> a = b.
Proof.
  intro a; induction a; intros [] H;
    simpl in *; inv H; f_equal; auto.
Qed.

Lemma string_of_uint_inj : forall a b,
    NilZero.string_of_uint a = NilZero.string_of_uint b -> a = b.
Proof.
  unfold NilZero.string_of_uint.
  intros [] [] H; simpl in *; inv H; auto.
  - destruct u; simpl in *.
Abort.

Lemma to_little_uint_comm : forall n d,
    Nat.to_little_uint n d =
    Nat.to_little_uint (Nat.of_uint d) (Nat.to_uint n).
Proof.
  intro n; induction n as [| n IHn];
    intros []; cbn in *.
Abort.

Lemma nat_to_uint_inj : forall m n,
    Nat.to_uint m = Nat.to_uint n -> m = n.
Proof.
  intro m; induction m as [| m IHm];
    intros [| n] H; cbn in *; auto.
Abort.

(* Must be valid, but
   it seems there needs to be
   much machinery to prove. *)
Lemma string_of_unit_of_to_uint_inj : forall m n,
    NilZero.string_of_uint (Nat.to_uint m) =
    NilZero.string_of_uint (Nat.to_uint n) -> m = n.
Proof.
  intro m; induction m as [| m IHm];
    intros [| n] H; cbn in *; auto.
  - admit.
  - admit.
  - f_equal; apply IHm; clear IHm.
Admitted.
