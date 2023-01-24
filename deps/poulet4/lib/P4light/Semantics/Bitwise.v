From Coq Require Import Lists.List Arith.PeanoNat
     ZArith.BinInt NArith.BinNatDef.
Require Import Poulet4.Utils.P4Arith.
Require Import Coq.Sorting.Permutation.

Import ListNotations.

Open Scope bool_scope.
Open Scope nat_scope.

(* convenience functions for treating bits and nats as little-endian bitvectors *)

(* It would be nice to use Coq's Bvectors, but, dependently-typed vectors are a pain to work with.
   So instead we use a similar representation and expose options.
*)
Section Bitwise.
  Definition Bits := list bool.

  (* increment a bitvector *)
  Fixpoint incr (b: Bits) : Bits :=
    match b with
    | [] => []
    | true :: xs => false :: incr xs
    | false :: xs => true :: xs
    end.

  Definition zero (w: nat) : Bits := repeat false w.

  Definition length_zero: forall w, length (zero w) = w.
  Proof. intros. unfold zero. rewrite repeat_length. reflexivity. Qed.

  (* Much faster conversion *)
  Definition of_N (n : N) (w: nat)  :=
    let fix of_N' (n : N) (w : nat) :=
      match w with
      | O => []
      | S w' => (N.odd n) :: (of_N' (N.div2 n) w')
      end in
    of_N' (Z.to_N (BitArith.mod_bound (N.of_nat w) (Z.of_N n))) w.

  Lemma of_N_length: forall n w, length (of_N n w) = w.
  Proof.
    intros. unfold of_N.
    remember (fix of_N' (n0 : N) (w0 : nat) {struct w0} : list bool :=
                match w0 with
                | 0 => []
                | S w' => N.odd n0 :: of_N' (N.div2 n0) w'
                end) as of_N'. rename Heqof_N' into Hof.
    cut (forall x y, length (of_N' x y) = y).
    - intros. rewrite H. auto.
    - clear -Hof. intros. revert x. induction y; intros; rewrite Hof; simpl; auto.
      rewrite <- Hof. f_equal. apply IHy.
  Qed.

  Fixpoint to_N (bits : Bits) : N :=
    match bits with
    | [] => 0
    | h :: t => N.add (if h then 1 else 0) (N.mul 2 (to_N t))
    end.

  Definition of_nat (n: nat) (w: nat) := Nat.iter n incr (zero w).

  Fixpoint pow_two (w: nat) : nat :=
    match w with
    | 0     => 1
    | S w'  => Nat.double (pow_two w')
    end.

  Definition add_bit_carry (part_with_width : nat * nat) (bit: bool) : nat * nat :=
    let '(part, w) := part_with_width in
    match bit with
    | false =>  (part, w + 1)
    | true =>  (part + pow_two w, w + 1)
    end.

  Definition to_nat (bits: Bits) : nat := fst (fold_left add_bit_carry bits (0,0)).

  Lemma add_carry_zero : forall w k,
    fst (fold_left add_bit_carry (zero w) (0, k)) = 0.
  Proof.
    intros w.
    induction w; intros k; induction k; auto.
    - apply IHw.
    - apply IHw.
  Qed.

  Lemma to_nat_zero: forall w, to_nat (zero w) = 0.
  Proof.
    intros.
    unfold to_nat.
    apply add_carry_zero.
  Qed.

  Lemma to_of_nat_corr : forall w n,
    n < pow_two n -> to_nat (of_nat n w) = n.
  Proof.
    intros.
    induction n.
    - apply to_nat_zero.
  Abort.

  Definition slice {A} (w: nat) (bits: list A) (lo: nat) (hi: nat) : option (list A) :=
    if (hi <? w) && (lo <=? hi) then
    Some (firstn (w - hi) (skipn lo bits)) else
    None.

  Definition splice {A} (wl: nat) (lhs: list A) (lo: nat) (hi: nat) (wr: nat) (rhs: list A) : option (list A) :=
    if (lo <=? hi) && (wr <=? (hi - lo + 1)) then
    let pref := firstn lo lhs in
    let suff := skipn (wl - hi + 1) lhs in
    Some (pref ++ rhs ++ suff) else
    None.

  (* Conversion with big-endian bit vectors *)
  Definition little_to_big (bits: Bits) : Bits := rev bits.

  Definition big_to_little (bits: Bits) : Bits := rev bits.

  Fixpoint map2 {A : Type} (f : A -> A -> A) (l1 : list A) (l2 : list A) : (list A) :=
    match l1, l2 with
    | [], _ => l2
    | _, []  => l1
    | h1 :: t1, h2 :: t2 => (f h1 h2) :: (map2 f t1 t2)
    end.

  Lemma map2_length: forall {A: Type} f (l1 l2: list A),
      length (map2 f l1 l2) = max (length l1) (length l2).
  Proof.
    intros. revert l1 l2. induction l1; simpl; intros; auto. destruct l2; simpl; auto.
  Qed.

  Lemma map2_nil_2: forall {A: Type} f (l: list A), map2 f l [] = l.
  Proof. intros. destruct l; simpl; reflexivity. Qed.

  Lemma map2_app: forall {A: Type} f (l1 l2 l3 l4: list A),
      length l1 = length l2 -> map2 f (l1 ++ l3) (l2 ++ l4) = map2 f l1 l2 ++ map2 f l3 l4.
  Proof.
    intros A f. induction l1; intros l2 l3 l4 Hl12.
    - destruct l2. 2: simpl in Hl12; inversion Hl12. simpl. reflexivity.
    - destruct l2 as [|b l2]. 1: simpl in Hl12; inversion Hl12. simpl.
      rewrite IHl1. 1: reflexivity. simpl in Hl12. inversion Hl12. reflexivity.
  Qed.

  Lemma map2_nth: forall {A: Type} f (l1 l2: list A) d1 d2 n,
      length l1 = length l2 -> nth n (map2 f l1 l2) (f d1 d2) = f (nth n l1 d1) (nth n l2 d2).
  Proof.
    intros A f. induction l1; intros l2 d1 d2 n Hl12.
    - destruct l2. 2: simpl in Hl12; inversion Hl12. simpl; destruct n; reflexivity.
    - destruct l2 as [|b l2]. 1: simpl in Hl12; inversion Hl12. simpl. destruct n; auto.
  Qed.

  Definition xor := map2 xorb.

  Infix "⦻" := xor (at level 38, left associativity).

  Lemma xor_length: forall l1 l2, length (l1 ⦻ l2) = max (length l1) (length l2).
  Proof. intros. unfold xor. apply map2_length. Qed.

  Lemma xor_assoc: forall l1 l2 l3, l1 ⦻ l2 ⦻ l3 = l1 ⦻ (l2 ⦻ l3).
  Proof.
    unfold xor. induction l1; intros; simpl. 1: reflexivity. destruct l2.
    - simpl. destruct l3; reflexivity.
    - destruct l3; simpl. 1: reflexivity. rewrite IHl1, Bool.xorb_assoc_reverse. reflexivity.
  Qed.

  Lemma xor_comm: forall l1 l2, l1 ⦻ l2 = l2 ⦻ l1.
  Proof.
    unfold xor. induction l1; intros; simpl. 1: rewrite map2_nil_2; reflexivity.
    destruct l2. 1: easy. simpl. rewrite IHl1, Bool.xorb_comm. reflexivity.
  Qed.

  Lemma xor_nilpotent: forall l, l ⦻ l = zero (length l).
  Proof.
    unfold xor. induction l; simpl. 1: reflexivity.
    rewrite Bool.xorb_nilpotent, IHl. reflexivity.
  Qed.

  Lemma xor_false_l: forall l n, n <= length l -> (zero n) ⦻ l = l.
  Proof.
    unfold xor. induction l; intros n Hl; destruct n; simpl in *.
    - reflexivity.
    - apply Nat.nle_succ_0 in Hl. easy.
    - reflexivity.
    - rewrite IHl. 2: now apply le_S_n. destruct a; reflexivity.
  Qed.

  Lemma xor_false_r: forall l n, n <= length l -> l ⦻ (zero n) = l.
  Proof. intros l n Hl. rewrite xor_comm, xor_false_l; easy. Qed.

  Lemma xor_affine: forall x a b c, (x ⦻ a) ⦻ (x ⦻ b) ⦻ (x ⦻ c) = x ⦻ (a ⦻ b ⦻ c).
  Proof.
    intros x a b c. rewrite <- !xor_assoc, (xor_comm (x ⦻ a ⦻ x ⦻ b)),
      (xor_comm (x ⦻ a)), !xor_assoc, <- !xor_assoc, xor_nilpotent, xor_false_l; easy.
  Qed.

  Lemma xor_rev_linear: forall l1 l2,
      length l1 = length l2 -> rev (l1 ⦻ l2) = (rev l1) ⦻ (rev l2).
  Proof.
    unfold xor. induction l1; intros l2 Hl12; simpl. 1: reflexivity. destruct l2.
    1: simpl in Hl12; inversion Hl12. simpl in *. inversion Hl12. clear Hl12.
    rewrite map2_app. 2: now rewrite !rev_length. rewrite IHl1; easy.
  Qed.

  Lemma xor_cons: forall a la b lb, (a :: la) ⦻ (b :: lb) = xorb a b :: (la ⦻ lb).
  Proof. intros. unfold xor. simpl. reflexivity. Qed.

  Lemma xor_nil_l: forall l, [] ⦻ l = l.
  Proof. intros. unfold xor. simpl. reflexivity. Qed.

  Lemma xor_nil_r: forall l, l ⦻ [] = l.
  Proof. intros. rewrite xor_comm. apply xor_nil_l. Qed.

  Lemma zero_app_xor_linear: forall n l1 l2,
      zero n ++ (l1 ⦻ l2) = (zero n ++ l1) ⦻ (zero n ++ l2).
  Proof.
    intros n l1 l2. unfold xor. rewrite map2_app; auto. fold xor.
    rewrite xor_false_l; auto. rewrite length_zero. easy.
  Qed.

  Definition pos_manip_func {A: Type} (f: list A -> list A): Prop :=
    forall n, exists S, forall a l, length l = n -> f l = map (fun i => nth i l a) S.

  Lemma map_xor {A}: forall (f1 f2: A -> bool) l,
      map f1 l ⦻ map f2 l = map (fun x => xorb (f1 x) (f2 x)) l.
  Proof.
    intros f1 f2. induction l; simpl. 1: reflexivity.
    rewrite xor_cons. rewrite IHl. reflexivity.
  Qed.

  Lemma pos_manip_func_xor_linear: forall f l1 l2,
      length l1 = length l2 -> pos_manip_func f -> f (l1 ⦻ l2) = f l1 ⦻ f l2.
  Proof.
    intros f l1 l2 Hl12 Hf. remember (length l1) as n eqn: Hl1.
    remember (length l2) as m eqn: Hl2. rewrite <- Hl12 in Hl2. clear dependent m.
    symmetry in Hl1, Hl2. specialize (Hf n). destruct Hf as [S Hf].
    rewrite (Hf false l1), (Hf false l2), (Hf false (l1 ⦻ l2)), map_xor; auto.
    2: rewrite xor_length, Hl1, Hl2, Nat.max_id; reflexivity.
    apply nth_ext with (d := false) (d' := false). 1: rewrite !map_length; reflexivity.
    intros j Hlt. remember (fun x : _ => xorb _ _) as g eqn: Hg.
    rewrite (map_ext g (fun x => nth x (l1 ⦻ l2) false)); auto. subst g.
    unfold xor. intros i. rewrite <- (Bool.xorb_false_l false) at 3.
    rewrite map2_nth; intuition.
  Qed.

End Bitwise.

(* Compute slice 4 [false; true; true; false] 1 2. *)
(* Compute splice 5 [false; false; false; false; false] 2 3 2 [true; true]. *)
