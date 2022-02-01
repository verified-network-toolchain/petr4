From Coq Require Import Lists.List Arith.PeanoNat
     ZArith.BinInt NArith.BinNatDef.
Require Import Poulet4.Utils.P4Arith.

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
    Admitted.

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

  Definition xor := map2 xorb.

End Bitwise.

(* Compute slice 4 [false; true; true; false] 1 2. *)
(* Compute splice 5 [false; false; false; false; false] 2 3 2 [true; true]. *)
